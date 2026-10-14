// deploy: the taproot output of a program and the transactions that spend it.
//
//   deploy compile <program.simpl> <out>
//       parse (minutes for a large program) and finalize without pruning; writes <out>.uprog, the consensus
//       encoding of the unpruned program, which the other commands decode in a second; prints the CMR
//   deploy address <program> <network> [--internal-key <x-only hex> | --secret <hex>]
//       the CMR, the output key and the address of a taproot output with one Simplicity leaf (version 0xbe,
//       script = the CMR) and the internal key (default: BIP341's unspendable point, i.e. no key path; with
//       --secret the key of that secret, every command accepts either)
//   deploy sighash <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex>]
//       the sig_all_hash of input 0 of the spending transaction below: leaf 0 of the circuit's public-signal tree
//   deploy spend <program> <witness.json> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex>] [--save <out>]
//       the transaction spending the output with the proof: one input whose witness stack is the Simplicity
//       witness, the program, the CMR and the control block, one explicit output of sats - fee to dest and the
//       fee output; the program is pruned against this transaction and executed, then the hex is printed
//       (--save also writes the pruned <out>.prog and <out>.wit; given those two files instead of the program
//       and the witness spec, the transaction is built from them without executing, e.g. to show a rejection)
//   deploy keyspend <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> --secret <hex> [--genesis <hash>]
//       the same transaction spent through the key path, with a Schnorr signature of the internal key's secret
//   deploy wallet <network> --secret <hex> [--blinding <hex>]
//       the P2WPKH address of the secret's key, unconfidential and (with a blinding key) confidential, to
//       receive coins from any wallet
//   deploy send <network> <funding.hex> <vout> <dest> <sats> <fee> --secret <hex> [--blinding <hex>] [--change <address>]
//       spends output <vout> of the funding transaction (the raw hex in a file; unblinded with the blinding
//       key if confidential) to dest as an explicit output of sats, e.g. to fund a verifier address; the rest
//       minus the fee goes to the change address, blinded when the input was (the blinders must balance)
//   deploy sighash dummy
//       the sig_all_hash of the harness's dummy environment (tests)
//
// <program> is a .uprog file, the .simpl text (parsed, slow) or, except for spend, the CMR in hex.  <network> is
// elementsregtest, liquidtestnet or liquid; --genesis is the chain's `getblockhash 0`, needed on elementsregtest
// where the genesis block depends on the node's configuration (the Liquid hashes are built in).
use groth_harness::witness::{self, hex, hex_to_bytes};
use groth_harness::env;
use simplicity::elements::encode::serialize_hex;
use simplicity::elements::secp256k1_zkp as secp;
use simplicity::elements::sighash::{Prevouts, SchnorrSighashType, SighashCache};
use simplicity::elements::{bitcoin, EcdsaSighashType};
use simplicity::elements::taproot::{TaprootBuilder, TaprootSpendInfo};
use simplicity::elements::{confidential, Address, AddressParams, AssetId, BlockHash, LockTime, OutPoint, Script, Sequence, Transaction, TxIn, TxInWitness, TxOut, TxOutWitness, Txid, Witness};
use simplicity::human_encoding::Forest;
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicity::jet::Elements;
use simplicity::{types, BitIter, BitMachine, BitWriter, Cmr, CommitNode, RedeemNode, Value};
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

const NUMS_KEY: &str = "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"; // BIP341's unspendable point
const LIQUID_GENESIS: &str = "1466275836220db2944ca059a3a10ef6fd2ea684b0688d2c379296888a206003";
const LIQUID_TESTNET_GENESIS: &str = "a771da8e52ee6ad581ed1e9a99825e5b3b7992225534eaa2ae23244fe26ab1c1";

fn params(network: &str) -> &'static AddressParams {
    match network {
        "elementsregtest" | "regtest" => &AddressParams::ELEMENTS,
        "liquidtestnet" => &AddressParams::LIQUID_TESTNET,
        "liquid" | "liquidv1" => &AddressParams::LIQUID,
        _ => panic!("unknown network {} (elementsregtest | liquidtestnet | liquid)", network),
    }
}

fn genesis(network: &str, flag: Option<&String>) -> BlockHash {
    let h = match (flag, network) {
        (Some(h), _) => h.as_str(),
        (None, "liquid") | (None, "liquidv1") => LIQUID_GENESIS,
        (None, "liquidtestnet") => LIQUID_TESTNET_GENESIS,
        _ => panic!("--genesis <hash> is needed on {} (elements-cli getblockhash 0)", network),
    };
    BlockHash::from_str(h).expect("genesis block hash")
}

/// positional arguments and --flag value options
fn parse_args(args: &[String]) -> (Vec<String>, HashMap<String, String>) {
    let mut pos = Vec::new();
    let mut flags = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        if let Some(name) = args[i].strip_prefix("--") {
            flags.insert(name.to_string(), args.get(i + 1).expect("flag value").clone());
            i += 2;
        } else {
            pos.push(args[i].clone());
            i += 1;
        }
    }
    (pos, flags)
}

/// parse the human-readable program and finalize it without pruning (unpopulated witness nodes get zero values)
fn parse_unpruned(path: &str) -> Arc<RedeemNode> {
    let t0 = std::time::Instant::now();
    let prog = std::fs::read_to_string(path).unwrap();
    let node = types::Context::with_context(|ctx| {
        let forest = Forest::parse::<Elements>(&prog).expect("parse");
        eprintln!("parsed in {:.1}s", t0.elapsed().as_secs_f64());
        let node = forest.to_witness_node(&ctx, &HashMap::new()).expect("no main");
        node.finalize_unpruned().expect("finalize")
    });
    eprintln!("finalized in {:.1}s", t0.elapsed().as_secs_f64());
    node
}

/// the CMR of a program given as .uprog, .simpl or hex
fn program_cmr(arg: &str) -> [u8; 32] {
    if arg.len() == 64 && arg.chars().all(|c| c.is_ascii_hexdigit()) {
        return hex_to_bytes(arg).try_into().unwrap();
    }
    if arg.ends_with(".uprog") || arg.ends_with(".prog") {
        let p = std::fs::read(arg).unwrap();
        let node = CommitNode::decode::<_, Elements>(BitIter::from(p.iter().cloned())).expect("decode");
        return node.cmr().to_byte_array();
    }
    parse_unpruned(arg).cmr().to_byte_array()
}

/// the unpruned program with the witness bound: from .uprog + the witness spec, or the .simpl text
fn program_with_witness(arg: &str, witness_path: &str) -> Arc<RedeemNode> {
    let w = witness::load_single(witness_path);
    if arg.ends_with(".uprog") {
        let p = std::fs::read(arg).unwrap();
        let mut wbytes = Vec::new();
        {
            let mut bw = BitWriter::new(&mut wbytes);
            simplicity::encode_value(&w, &mut bw).unwrap();
            bw.flush_all().unwrap();
        }
        return RedeemNode::decode::<_, _, Elements>(BitIter::from(p.iter().cloned()), BitIter::from(wbytes.iter().cloned())).expect("decode with witness");
    }
    let t0 = std::time::Instant::now();
    let prog = std::fs::read_to_string(arg).unwrap();
    let mut witness: HashMap<Arc<str>, Value> = HashMap::new();
    witness.insert(Arc::from("w_in"), w);
    let node = types::Context::with_context(|ctx| {
        let forest = Forest::parse::<Elements>(&prog).expect("parse");
        eprintln!("parsed in {:.1}s", t0.elapsed().as_secs_f64());
        let node = forest.to_witness_node(&ctx, &witness).expect("no main");
        node.finalize_unpruned().expect("finalize")
    });
    node
}

fn spend_info(cmr: &[u8; 32], internal_key: &str) -> (TaprootSpendInfo, Script, secp::XOnlyPublicKey) {
    let secp_ctx = secp::Secp256k1::verification_only();
    let key = secp::XOnlyPublicKey::from_str(internal_key).expect("internal key (x-only, hex)");
    let script = Script::from(cmr.to_vec());
    let info = TaprootBuilder::new()
        .add_leaf_with_ver(0, script.clone(), simplicity::leaf_version())
        .expect("leaf")
        .finalize(&secp_ctx, key)
        .expect("finalize taproot");
    (info, script, key)
}

struct Spend {
    tx: Transaction,
    utxo: TxOut,
    info: TaprootSpendInfo,
    script: Script,
}

/// the transaction spending <txid>:<vout> (sats of asset, held by the verifier's output) to dest minus the fee
fn spend_tx(cmr: &[u8; 32], internal_key: &str, network: &'static AddressParams, pos: &[String]) -> Spend {
    let txid = Txid::from_str(&pos[0]).expect("txid");
    let vout: u32 = pos[1].parse().expect("vout");
    let sats: u64 = pos[2].parse().expect("amount in satoshis");
    let asset = AssetId::from_str(&pos[3]).expect("asset id");
    let dest = Address::parse_with_params(&pos[4], network).expect("destination address");
    let fee: u64 = pos[5].parse().expect("fee in satoshis");
    let (info, script, key) = spend_info(cmr, internal_key);
    let secp_ctx = secp::Secp256k1::verification_only();
    let address = Address::p2tr(&secp_ctx, key, info.merkle_root(), None, network);
    let utxo = TxOut {
        asset: confidential::Asset::Explicit(asset),
        value: confidential::Value::Explicit(sats),
        nonce: confidential::Nonce::Null,
        script_pubkey: address.script_pubkey(),
        witness: TxOutWitness::default(),
    };
    let tx = Transaction {
        version: 2,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint { txid, vout },
            is_pegin: false,
            script_sig: Script::new(),
            sequence: Sequence::MAX,
            asset_issuance: Default::default(),
            witness: TxInWitness::default(),
        }],
        output: vec![
            TxOut {
                asset: confidential::Asset::Explicit(asset),
                value: confidential::Value::Explicit(sats.checked_sub(fee).expect("the fee exceeds the amount")),
                nonce: confidential::Nonce::Null,
                script_pubkey: dest.script_pubkey(),
                witness: TxOutWitness::default(),
            },
            TxOut::new_fee(fee, asset),
        ],
    };
    Spend { tx, utxo, info, script }
}

/// the Simplicity environment of input 0 of the spend
fn environment(spend: &Spend, cmr: &[u8; 32], genesis_hash: BlockHash) -> ElementsEnv<Arc<Transaction>> {
    let control = spend.info.control_block(&(spend.script.clone(), simplicity::leaf_version())).unwrap();
    ElementsEnv::new(Arc::new(spend.tx.clone()), vec![ElementsUtxo::from(spend.utxo.clone())], 0,
                     Cmr::from_byte_array(*cmr), control, None, genesis_hash)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (pos, flags) = parse_args(&args);
    let cmd = pos.first().map(String::as_str).unwrap_or("");
    let internal_key = match (flags.get("internal-key"), flags.get("secret")) {
        (Some(k), _) => k.clone(),
        (None, Some(sk)) => secp::Keypair::from_seckey_str(&secp::Secp256k1::new(), sk).expect("secret key").x_only_public_key().0.to_string(),
        (None, None) => NUMS_KEY.to_string(),
    };
    let internal_key = internal_key.as_str();
    match cmd {
        "compile" => {
            let node = parse_unpruned(&pos[1]);
            let p = node.to_vec_without_witness();
            std::fs::write(format!("{}.uprog", pos[2]), &p).unwrap();
            println!("{{\"cmr\":\"{}\",\"unpruned_bytes\":{}}}", hex(&node.cmr().to_byte_array()), p.len());
        }
        "address" => {
            let cmr = program_cmr(&pos[1]);
            let network = params(&pos[2]);
            let (info, script, key) = spend_info(&cmr, internal_key);
            let secp_ctx = secp::Secp256k1::verification_only();
            let address = Address::p2tr(&secp_ctx, key, info.merkle_root(), None, network);
            let control = info.control_block(&(script, simplicity::leaf_version())).unwrap().serialize();
            println!("{{\"cmr\":\"{}\",\"internal_key\":\"{}\",\"output_key\":\"{}\",\"address\":\"{}\",\"script_pubkey\":\"{}\",\"control_block\":\"{}\"}}",
                     hex(&cmr), key, info.output_key().into_inner(), address, hex(address.script_pubkey().as_bytes()), hex(&control));
        }
        "sighash" if pos.get(1).map(String::as_str) == Some("dummy") => {
            println!("{}", hex(env::dummy().c_tx_env().sighash_all().as_ref()));
        }
        "sighash" => {
            let cmr = program_cmr(&pos[1]);
            let network = params(&pos[2]);
            let spend = spend_tx(&cmr, internal_key, network, &pos[3..]);
            let env = environment(&spend, &cmr, genesis(&pos[2], flags.get("genesis")));
            println!("{}", hex(env.c_tx_env().sighash_all().as_ref()));
        }
        "spend" => {
            let network = params(&pos[3]);
            let t0 = std::time::Instant::now();
            let (p, w, cmr, cost) = if pos[1].ends_with(".prog") {
                // the pruned encodings saved by an earlier spend: decoded for the CMR and the cost, not executed
                let p = std::fs::read(&pos[1]).unwrap();
                let w = std::fs::read(&pos[2]).unwrap();
                let decoded = RedeemNode::decode::<_, _, Elements>(BitIter::from(p.iter().cloned()), BitIter::from(w.iter().cloned())).expect("decode");
                let cost = decoded.bounds().cost.to_string().parse::<u64>().unwrap();
                (p, w, decoded.cmr().to_byte_array(), cost)
            } else {
                let unpruned = program_with_witness(&pos[1], &pos[2]);
                let cmr = unpruned.cmr().to_byte_array();
                eprintln!("program loaded in {:.1}s", t0.elapsed().as_secs_f64());
                let spend = spend_tx(&cmr, internal_key, network, &pos[4..]);
                let env = environment(&spend, &cmr, genesis(&pos[3], flags.get("genesis")));
                let program = unpruned.prune(&env).expect("the program fails on this witness and transaction");
                let mut mac = BitMachine::for_program(&program).expect("machine");
                mac.exec(&program, &env).expect("the pruned program fails");
                let (p, w) = program.to_vec_with_witness();
                let cost = program.bounds().cost.to_string().parse::<u64>().unwrap();
                eprintln!("pruned and executed in {:.1}s", t0.elapsed().as_secs_f64());
                if let Some(out) = flags.get("save") {
                    std::fs::write(format!("{}.prog", out), &p).unwrap();
                    std::fs::write(format!("{}.wit", out), &w).unwrap();
                }
                (p, w, cmr, cost)
            };
            let mut spend = spend_tx(&cmr, internal_key, network, &pos[4..]);
            let control = spend.info.control_block(&(spend.script.clone(), simplicity::leaf_version())).unwrap().serialize();
            spend.tx.input[0].witness.script_witness = Witness::from_slice(&[w.clone(), p.clone(), cmr.to_vec(), control.clone()]);
            let stack_bytes = p.len() + w.len() + 32 + control.len() + 4 + 1; // items with CompactSize prefixes
            let budget = (stack_bytes + 50) * 1000;
            eprintln!("cost {} mWU, program {} bytes, witness {} bytes, witness stack {} bytes (budget {} mWU, covered: {}), tx weight {} WU",
                      cost, p.len(), w.len(), stack_bytes, budget, cost <= budget as u64, spend.tx.weight());
            println!("{}", serialize_hex(&spend.tx));
        }
        "wallet" => {
            let network = params(&pos[1]);
            let secp_ctx = secp::Secp256k1::new();
            let keypair = secp::Keypair::from_seckey_str(&secp_ctx, flags.get("secret").expect("--secret <hex>")).expect("secret key");
            let pk = bitcoin::PublicKey::new(keypair.public_key());
            let blinder = flags.get("blinding").map(|bk| secp::PublicKey::from_secret_key(&secp_ctx, &secp::SecretKey::from_str(bk).expect("blinding key")));
            println!("{{\"pubkey\":\"{}\",\"address\":\"{}\",\"confidential_address\":\"{}\"}}", pk, Address::p2wpkh(&pk, None, network),
                     blinder.map(|b| Address::p2wpkh(&pk, Some(b), network).to_string()).unwrap_or_default());
        }
        "send" => {
            let network = params(&pos[1]);
            let secp_ctx = secp::Secp256k1::new();
            let keypair = secp::Keypair::from_seckey_str(&secp_ctx, flags.get("secret").expect("--secret <hex>")).expect("secret key");
            let pk = bitcoin::PublicKey::new(keypair.public_key());
            let funding: Transaction = simplicity::elements::encode::deserialize(&hex_to_bytes(std::fs::read_to_string(&pos[2]).unwrap().trim())).expect("funding transaction hex");
            let vout: u32 = pos[3].parse().expect("vout");
            let utxo = funding.output[vout as usize].clone();
            assert_eq!(utxo.script_pubkey, Address::p2wpkh(&pk, None, network).script_pubkey(), "the output does not pay the key");
            let dest = Address::parse_with_params(&pos[4], network).expect("destination address");
            let sats: u64 = pos[5].parse().expect("amount in satoshis");
            let fee: u64 = pos[6].parse().expect("fee in satoshis");
            // the input: explicit, or unblinded with the blinding key
            let secrets = match (utxo.value, utxo.asset) {
                (confidential::Value::Explicit(v), confidential::Asset::Explicit(a)) => simplicity::elements::TxOutSecrets::new(a, confidential::AssetBlindingFactor::zero(), v, confidential::ValueBlindingFactor::zero()),
                _ => utxo.unblind(&secp_ctx, secp::SecretKey::from_str(flags.get("blinding").expect("--blinding <hex> for a confidential input")).unwrap()).expect("unblind"),
            };
            let confidential = utxo.value.is_confidential();
            let change = secrets.value.checked_sub(sats + fee).expect("the input does not cover the amount and the fee");
            eprintln!("input: {} sats of {}{}", secrets.value, secrets.asset, if confidential { " (confidential)" } else { "" });
            let mut outputs = vec![TxOut {
                asset: confidential::Asset::Explicit(secrets.asset),
                value: confidential::Value::Explicit(sats),
                nonce: confidential::Nonce::Null,
                script_pubkey: dest.script_pubkey(),
                witness: TxOutWitness::default(),
            }];
            if confidential || change > 0 {
                // a confidential input needs a confidential output for the blinders to balance: the change
                let change_addr = Address::parse_with_params(flags.get("change").expect("--change <address>"), network).expect("change address");
                if confidential {
                    let blinder = change_addr.blinding_pubkey.expect("the change address must be confidential");
                    let (txout, _, _, _) = TxOut::new_last_confidential(&mut secp::rand::thread_rng(), &secp_ctx, change, secrets.asset, change_addr.script_pubkey(), blinder, &[secrets], &[]).expect("blind the change");
                    outputs.push(txout);
                } else {
                    outputs.push(TxOut { asset: confidential::Asset::Explicit(secrets.asset), value: confidential::Value::Explicit(change), nonce: confidential::Nonce::Null, script_pubkey: change_addr.script_pubkey(), witness: TxOutWitness::default() });
                }
            }
            outputs.push(TxOut::new_fee(fee, secrets.asset));
            let mut tx = Transaction {
                version: 2,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: OutPoint { txid: funding.txid(), vout },
                    is_pegin: false,
                    script_sig: Script::new(),
                    sequence: Sequence::MAX,
                    asset_issuance: Default::default(),
                    witness: TxInWitness::default(),
                }],
                output: outputs,
            };
            let script_code = Script::new_p2pkh(&pk.pubkey_hash());
            let sighash = SighashCache::new(&tx).segwitv0_sighash(0, &script_code, utxo.value, EcdsaSighashType::All);
            let sig = secp_ctx.sign_ecdsa(&secp::Message::from_digest(sighash.to_byte_array()), &keypair.secret_key());
            let mut sig_bytes = sig.serialize_der().to_vec();
            sig_bytes.push(EcdsaSighashType::All as u8);
            tx.input[0].witness.script_witness = Witness::from_slice(&[sig_bytes, pk.to_bytes()]);
            eprintln!("to {}: {} sats, change {} sats, fee {} sats, tx weight {} WU", pos[4], sats, change, fee, tx.weight());
            println!("{}", serialize_hex(&tx));
        }
        "keyspend" => {
            let cmr = program_cmr(&pos[1]);
            let network = params(&pos[2]);
            let secp_ctx = secp::Secp256k1::new();
            let keypair = secp::Keypair::from_seckey_str(&secp_ctx, flags.get("secret").expect("--secret <hex>")).expect("secret key");
            let (xonly, _) = keypair.x_only_public_key();
            let mut spend = spend_tx(&cmr, internal_key, network, &pos[3..]);
            let genesis_hash = genesis(&pos[2], flags.get("genesis"));
            let tweak = spend.info.tap_tweak().to_scalar();
            let tweaked = keypair.add_xonly_tweak(&secp_ctx, &tweak).expect("tweak");
            assert_eq!(tweaked.x_only_public_key().0, spend.info.output_key().into_inner(), "output key");
            let sighash = SighashCache::new(&spend.tx)
                .taproot_key_spend_signature_hash(0, &Prevouts::All(&[spend.utxo.clone()]), SchnorrSighashType::Default, genesis_hash)
                .expect("sighash");
            let sig = secp_ctx.sign_schnorr_no_aux_rand(&secp::Message::from_digest(sighash.to_byte_array()), &tweaked);
            spend.tx.input[0].witness.script_witness = Witness::from_slice(&[sig.as_ref().to_vec()]);
            eprintln!("key path: internal key {}, output key {}, tx weight {} WU", xonly, spend.info.output_key().into_inner(), spend.tx.weight());
            println!("{}", serialize_hex(&spend.tx));
        }
        _ => {
            eprintln!("usage: deploy compile <program.simpl> <out>\n       deploy address <program> <network> [--internal-key <hex> | --secret <hex>]\n       deploy sighash <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex>]\n       deploy spend <program> <witness.json> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex>] [--save <out>]\n       deploy keyspend <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> --secret <hex> [--genesis <hash>]\n       deploy wallet <network> --secret <hex> [--blinding <hex>]\n       deploy send <network> <funding.hex> <vout> <dest> <sats> <fee> --secret <hex> [--blinding <hex>] [--change <address>]\n       deploy sighash dummy");
            std::process::exit(2);
        }
    }
}
