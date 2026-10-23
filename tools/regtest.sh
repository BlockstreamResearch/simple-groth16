#!/usr/bin/env bash
# The toy circuit on an Elements regtest node:
#   1. fund the verifier's output, prove the statement for the transaction that spends it, spend;
#   2. show that the same proof is rejected in a transaction paying someone else;
#   3. spend an output of the same leaf with a real internal key through its key path.
#
#   tools/regtest.sh build/multiplier
#
# Before: `python3 tools/circom_demo.py setup --out build/multiplier` and
# `deploy compile build/multiplier/verifier.simpl build/multiplier/verifier`.  The fflonk verifier runs
# the same way, from `setup --protocol fflonk [--transcript sha256]` (its transaction is about 32 kvB).
#
# The node needs Simplicity enabled and a funded wallet.  elements.conf:
#     chain=elementsregtest
#     [elementsregtest]
#     server=1
#     validatepegin=0
#     evbparams=simplicity:-1:::
#     acceptnonstdtxn=0
#     initialfreecoins=2100000000000000
#     anyonecanspend_aremine=1
# then `elements-cli createwallet w` and `elements-cli rescanblockchain` to claim the free coins.
#
# Environment: ELEMENTS_CLI (default `elements-cli`, e.g. "elements-cli -datadir=..."), DEPLOY (the
# deploy binary), FEE in satoshis (100000 is about 7.5 sat/vB for this 13.3 kvB transaction), SECRET (the
# key path's secret in hex; by default the one in $OUT/keypath.secret, or a fresh one written there).
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=${1:?build directory, e.g. build/multiplier}
CLI=${ELEMENTS_CLI:-elements-cli}
DEPLOY=${DEPLOY:-$ROOT/tools/harness/target/release/deploy}
NET=elementsregtest
FEE=${FEE:-100000}
SATS=100000000 # every output is funded with 1.0
PROG=$OUT/verifier.uprog
# the key path's secret, in a file so that it appears in no command line: SECRET, or the one of an earlier
# run, or a fresh one
SECRET_FILE=$OUT/keypath.secret
if [ -n "${SECRET:-}" ]; then
  (umask 077 && printf '%s\n' "$SECRET" > "$SECRET_FILE")
elif [ ! -s "$SECRET_FILE" ]; then
  (umask 077 && python3 -c 'import secrets; print(secrets.token_hex(32))' > "$SECRET_FILE")
fi

json() { python3 -c "import json,sys; print(json.load(sys.stdin)[\"$1\"])"; }
unconfidential() { $CLI getaddressinfo "$1" | json unconfidential; }
genesis=$($CLI getblockhash 0)
asset=$($CLI dumpassetlabels | json bitcoin)
dest=$(unconfidential "$($CLI getnewaddress "" bech32)")

# fund <address> <script_pubkey>: send 1.0, mine it, set $fund (txid) and $vout
fund() {
  fund=$($CLI sendtoaddress "$1" 1.0)
  $CLI generatetoaddress 1 "$dest" > /dev/null
  vout=$($CLI getrawtransaction "$fund" true | python3 -c "
import json,sys; j=json.load(sys.stdin); print([o['n'] for o in j['vout'] if o['scriptPubKey'].get('hex') == '$2'][0])")
  echo "funded $fund:$vout with 1.0"
}

# accept <hex file>: testmempoolaccept
accept() { printf '["%s"]\n' "$(cat "$1")" | $CLI -stdin testmempoolaccept; }

# rejected <hex file>: testmempoolaccept must refuse it for its script (here: the Simplicity program fails)
rejected() {
  printf '["%s"]\n' "$(cat "$1")" | $CLI -stdin testmempoolaccept | python3 -c "
import json, sys
r = json.load(sys.stdin)[0]
print(json.dumps(r, indent=2))
reason = r.get('reject-reason', '')
sys.exit(0 if not r['allowed'] and 'script-verify' in reason and 'jet' in reason else 'not rejected by the program')"
}

# mine <hex file> <label>: send, mine, report
mine() {
  local txid
  txid=$($CLI -stdin sendrawtransaction < "$1")
  $CLI generatetoaddress 1 "$dest" > /dev/null
  $CLI getrawtransaction "$txid" true | python3 -c "
import json,sys; j=json.load(sys.stdin); print('$2 in tx {}: confirmations {}, weight {:,} WU, vsize {:,}'.format(j['txid'], j['confirmations'], j['weight'], j['vsize']))"
}

# 1. an output whose only spending condition is a proof for the spending transaction
info=$("$DEPLOY" address "$PROG" $NET)
addr=$(echo "$info" | json address)
echo "verifier address (no key path): $addr"
fund "$addr" "$(echo "$info" | json script_pubkey)"
sighash=$("$DEPLOY" sighash "$PROG" $NET "$fund" "$vout" $SATS "$asset" "$dest" "$FEE" --genesis "$genesis")
echo "sighash of the spending transaction: $sighash"
python3 "$ROOT/tools/circom_demo.py" prove --out "$OUT" --sighash "$sighash"
"$DEPLOY" spend "$PROG" "$OUT/verifier.w0.json" $NET "$fund" "$vout" $SATS "$asset" "$dest" "$FEE" --genesis "$genesis" > "$OUT/spend.hex"
accept "$OUT/spend.hex"
mine "$OUT/spend.hex" "spent with the proof"

# 2. the same proof in a transaction paying someone else (the output script replaced in the hex)
dest2=$(unconfidential "$($CLI getnewaddress "" bech32)")
spk1=$($CLI getaddressinfo "$dest" | json scriptPubKey); spk2=$($CLI getaddressinfo "$dest2" | json scriptPubKey)
fund "$addr" "$(echo "$info" | json script_pubkey)"
sighash=$("$DEPLOY" sighash "$PROG" $NET "$fund" "$vout" $SATS "$asset" "$dest" "$FEE" --genesis "$genesis")
python3 "$ROOT/tools/circom_demo.py" prove --out "$OUT" --sighash "$sighash" > /dev/null
"$DEPLOY" spend "$PROG" "$OUT/verifier.w0.json" $NET "$fund" "$vout" $SATS "$asset" "$dest" "$FEE" --genesis "$genesis" 2> /dev/null > "$OUT/spend2.hex"
sed "s/$spk1/$spk2/" "$OUT/spend2.hex" > "$OUT/redirected.hex"
if cmp -s "$OUT/spend2.hex" "$OUT/redirected.hex"; then
  echo "the output script of $dest is not in the transaction" >&2
  exit 1
fi
echo "the proof for $dest, redirected to $dest2 (must be rejected):"
rejected "$OUT/redirected.hex"
mine "$OUT/spend2.hex" "spent as intended"

# 3. the key path: the same leaf with a real internal key
info=$("$DEPLOY" address "$PROG" $NET --secret-file "$SECRET_FILE")
addr=$(echo "$info" | json address)
echo "verifier address with a key path (internal key $(echo "$info" | json internal_key)): $addr"
fund "$addr" "$(echo "$info" | json script_pubkey)"
"$DEPLOY" keyspend "$PROG" $NET "$fund" "$vout" $SATS "$asset" "$dest" "$FEE" --secret-file "$SECRET_FILE" --genesis "$genesis" > "$OUT/keyspend.hex"
accept "$OUT/keyspend.hex"
mine "$OUT/keyspend.hex" "spent through the key path"
