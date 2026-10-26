// deploy: the taproot output of a program and the transactions that spend it.
//
//   deploy compile <program.simpl> <out>
//       parse (minutes for a large program); writes <out>.uprog, the consensus encoding of the unpruned
//       program (its witness nodes each kept apart), which the other commands decode in a second, and
//       <out>.wnames, the names of its witness nodes in the order the encoding reads their values; prints
//       the CMR
//   deploy address <program> <network> [--internal-key <x-only hex> | --secret-file <file>]
//       the CMR, the output key and the address of a taproot output with one Simplicity leaf (version 0xbe,
//       script = the CMR) and the internal key (default: BIP341's unspendable point, i.e. no key path; with
//       --secret-file the key of the secret in that file).  address, sighash, spend and keyspend take
//       either flag, and need the same one to find the output
//   deploy sighash <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex> | --secret-file <file>]
//       the sig_all_hash of input 0 of the spending transaction below: the value the proof binds (leaf 0 of
//       the Merkle tree, the first public input with --sighash-input, or fflonk's two limbs)
//   deploy spend <program> <witness.json> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex> | --secret-file <file>] [--save <out>] [--force]
//       the transaction spending the output with the proof: one input whose witness stack is the Simplicity
//       witness, the program, the CMR and the control block, one explicit output of sats - fee to dest and the
//       fee output; the program is pruned against this transaction and executed, then the hex is printed
//       (--save also writes the pruned <out>.prog and <out>.wit; given those two files instead of the program
//       and the witness spec, the transaction is built from them without executing, e.g. to show a rejection).
//       It refuses a spend that a node would not take: a program above the consensus cap on the Bit Machine's
//       cells, a cost the input's budget does not cover, a transaction above the standard weight; --force
//       prints it anyway
//   deploy keyspend <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> --secret-file <file> [--genesis <hash>]
//       the same transaction spent through the key path, with a Schnorr signature of the internal key's secret
//   deploy wallet <network> --secret-file <file> [--blinding-file <file>]
//       the P2WPKH address of the secret's key, unconfidential and (with a blinding key) confidential, to
//       receive coins from any wallet
//   deploy send <network> <funding.hex> <vout> <dest> <sats> <fee> --secret-file <file> [--blinding-file <file>] [--change <address>]
//       spends output <vout> of the funding transaction (the raw hex in a file; unblinded with the blinding
//       key if confidential) to dest as an explicit output of sats, e.g. to fund a verifier address; the rest
//       minus the fee goes to the change address, blinded when the input was (the blinders must balance).
//       --change is needed unless sats + fee spend the whole input
//   deploy sighash dummy
//       the sig_all_hash of the harness's dummy environment (tests)
//
// <program> is a .uprog file, the .simpl text (parsed, slow) or, except for spend, the CMR in hex.  <network> is
// elementsregtest, liquidtestnet or liquid; --genesis is the chain's `getblockhash 0`, needed on elementsregtest
// where the genesis block depends on the node's configuration (the Liquid hashes are built in).  Secret and
// blinding keys are read from files (--secret-file, --blinding-file: hex), so that they appear in no command
// line; --secret <hex> and --blinding <hex> still work.  A flag a command does not take is refused.
use groth_harness::env;
use groth_harness::witness::{self, hex, hex_to_bytes};
use simplicity::dag::{DagLike, MaxSharing};
use simplicity::elements::encode::serialize_hex;
use simplicity::elements::secp256k1_zkp as secp;
use simplicity::elements::sighash::{Prevouts, SchnorrSighashType, SighashCache};
use simplicity::elements::taproot::{TaprootBuilder, TaprootSpendInfo};
use simplicity::elements::{bitcoin, EcdsaSighashType};
use simplicity::elements::{
    confidential, Address, AddressParams, AssetId, AssetIssuance, BlockHash, LockTime, OutPoint, Script, Sequence,
    Transaction, TxIn, TxInWitness, TxOut, TxOutSecrets, TxOutWitness, Txid, Witness,
};
use simplicity::human_encoding::Forest;
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicity::jet::Elements;
use simplicity::node::Inner;
use simplicity::{types, BitIter, BitMachine, BitWriter, Cmr, CommitNode, RedeemNode, Value};
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::sync::Arc;

const NUMS_KEY: &str = "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"; // BIP341's unspendable point
const LIQUID_GENESIS: &str = "1466275836220db2944ca059a3a10ef6fd2ea684b0688d2c379296888a206003";
const LIQUID_TESTNET_GENESIS: &str = "a771da8e52ee6ad581ed1e9a99825e5b3b7992225534eaa2ae23244fe26ab1c1";
/// the consensus cap on the Bit Machine's cells (libsimplicity limitations.h); the bound rust-simplicity
/// computes is at least the one a node computes
const CELLS_MAX: usize = 5_242_880;
/// the largest transaction weight nodes relay by default
const STANDARD_WEIGHT: usize = 400_000;

const USAGE: &str = "usage: deploy compile <program.simpl> <out>
       deploy address <program> <network> [--internal-key <hex> | --secret-file <file>]
       deploy sighash <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex> | --secret-file <file>]
       deploy spend <program> <witness.json> <network> <txid> <vout> <sats> <asset> <dest> <fee> [--genesis <hash>] [--internal-key <hex> | --secret-file <file>] [--save <out>] [--force]
       deploy keyspend <program> <network> <txid> <vout> <sats> <asset> <dest> <fee> --secret-file <file> [--genesis <hash>]
       deploy wallet <network> --secret-file <file> [--blinding-file <file>]
       deploy send <network> <funding.hex> <vout> <dest> <sats> <fee> --secret-file <file> [--blinding-file <file>] [--change <address>]
       deploy sighash dummy
(--secret <hex> and --blinding <hex> in place of the files also work)";

/// the number of positional arguments of each command, the command included
fn positional(command: &str, second: Option<&str>) -> Option<usize> {
    match (command, second) {
        ("sighash", Some("dummy")) => Some(2),
        ("compile" | "address", _) => Some(3),
        ("sighash" | "keyspend", _) => Some(9),
        ("spend", _) => Some(10),
        ("wallet", _) => Some(2),
        ("send", _) => Some(7),
        _ => None,
    }
}

/// the flags each command takes; `force` has no value
const KEYS: &[&str] = &["internal-key", "secret", "secret-file"];
fn allowed_flags(command: &str) -> Vec<&'static str> {
    let (own, keys): (&[&str], bool) = match command {
        "compile" => (&[], false),
        "address" => (&[], true),
        "sighash" => (&["genesis"], true),
        "spend" => (&["genesis", "save", "force"], true),
        "keyspend" => (&["genesis"], true),
        "wallet" | "send" => (&["secret", "secret-file", "blinding", "blinding-file", "change"], false),
        _ => (&[], false),
    };
    own.iter().chain(if keys { KEYS } else { &[] }).copied().collect()
}

/// print the error and exit
fn fail(msg: &str) -> ! {
    eprintln!("deploy: {}", msg);
    std::process::exit(1)
}

type Flags = HashMap<String, String>;

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
        (None, "liquid" | "liquidv1") => LIQUID_GENESIS,
        (None, "liquidtestnet") => LIQUID_TESTNET_GENESIS,
        _ => panic!(
            "--genesis <hash> is needed on {} (elements-cli getblockhash 0)",
            network
        ),
    };
    BlockHash::from_str(h).expect("genesis block hash")
}

/// positional arguments and --flag value options; a flag the command does not take, a flag given twice,
/// or --flag=value is refused
fn parse_args(args: &[String]) -> (Vec<String>, Flags) {
    let mut pos = Vec::new();
    let mut flags = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        if let Some(name) = args[i].strip_prefix("--") {
            let value = if name == "force" {
                i += 1;
                String::new()
            } else {
                i += 2;
                match args.get(i - 1) {
                    Some(v) if !v.starts_with("--") => v.clone(),
                    _ => fail(&format!("--{} needs a value", name)),
                }
            };
            if flags.insert(name.to_string(), value).is_some() {
                fail(&format!("--{} is given twice", name));
            }
        } else {
            pos.push(args[i].clone());
            i += 1;
        }
    }
    let command = pos.first().map(String::as_str).unwrap_or("");
    // a wrong count, e.g. a flag mistyped with one dash or a dash from a document, read as an argument
    if positional(command, pos.get(1).map(String::as_str)).is_some_and(|n| n != pos.len()) {
        fail(&format!("wrong number of arguments for {}\n{}", command, USAGE));
    }
    let allowed = allowed_flags(command);
    for name in flags.keys() {
        if !allowed.contains(&name.as_str()) {
            fail(&format!(
                "{} does not take --{}\n{}",
                pos.first().map(String::as_str).unwrap_or("deploy"),
                name,
                USAGE
            ));
        }
    }
    // a key from a file: it then appears in no command line
    for key in ["secret", "blinding"] {
        if let Some(path) = flags.remove(&format!("{}-file", key)) {
            if flags.contains_key(key) {
                fail(&format!("--{} and --{}-file", key, key));
            }
            let text = std::fs::read_to_string(&path).unwrap_or_else(|e| fail(&format!("{}: {}", path, e)));
            flags.insert(key.to_string(), text.trim().to_string());
        }
    }
    (pos, flags)
}

/// the keypair of --secret
fn keypair(flags: &Flags) -> secp::Keypair {
    let secret = flags.get("secret").expect("--secret <hex>");
    secp::Keypair::from_seckey_str(&secp::Secp256k1::new(), secret).expect("secret key")
}

/// the taproot internal key: --internal-key, the key of the secret, or BIP341's unspendable point
fn internal_key(flags: &Flags) -> String {
    match (flags.get("internal-key"), flags.get("secret")) {
        (Some(k), Some(_)) => {
            let own = keypair(flags).x_only_public_key().0.to_string();
            if *k != own {
                fail(&format!("--internal-key {} is not the key of the secret ({})", k, own));
            }
            own
        }
        (Some(k), None) => k.clone(),
        (None, Some(_)) => keypair(flags).x_only_public_key().0.to_string(),
        (None, None) => NUMS_KEY.to_string(),
    }
}

/// parse the human-readable program and finalize it without pruning (witness nodes without a value get
/// zero values)
fn parse_text(path: &str, witness: &HashMap<Arc<str>, Value>) -> Arc<RedeemNode> {
    let t0 = std::time::Instant::now();
    let text = std::fs::read_to_string(path).unwrap();
    let node = types::Context::with_context(|ctx| {
        let forest = Forest::parse::<Elements>(&text).expect("parse");
        eprintln!("parsed in {:.1}s", t0.elapsed().as_secs_f64());
        let node = forest.to_witness_node(&ctx, witness).expect("no main");
        node.finalize_unpruned().expect("finalize")
    });
    eprintln!("finalized in {:.1}s", t0.elapsed().as_secs_f64());
    node
}

/// parse the human-readable program: its commitment (types finalized, no witness values), whose encoding
/// keeps every witness node apart, and the names of the witness nodes in the order of that encoding
fn parse_commit(path: &str) -> (Arc<CommitNode>, Vec<String>) {
    let t0 = std::time::Instant::now();
    let text = std::fs::read_to_string(path).unwrap();
    let forest = Forest::parse::<Elements>(&text).expect("parse");
    eprintln!("parsed in {:.1}s", t0.elapsed().as_secs_f64());
    let main = forest.roots().get("main").expect("no main").clone();
    let names = main
        .clone()
        .post_order_iter::<MaxSharing<_>>()
        .filter(|item| matches!(item.node.inner(), Inner::Witness(_)))
        .map(|item| item.node.name().to_string())
        .collect();
    (main.to_commit_node(), names)
}

/// the CMR of a program given as .uprog, .simpl or hex (a file of that name comes first)
fn program_cmr(arg: &str) -> [u8; 32] {
    if !std::path::Path::new(arg).exists() && arg.len() == 64 && arg.chars().all(|c| c.is_ascii_hexdigit()) {
        return hex_to_bytes(arg).try_into().unwrap();
    }
    if arg.ends_with(".uprog") || arg.ends_with(".prog") {
        let p = std::fs::read(arg).unwrap();
        let node = CommitNode::decode::<_, Elements>(BitIter::from(p.iter().copied())).expect("decode");
        return node.cmr().to_byte_array();
    }
    parse_text(arg, &HashMap::new()).cmr().to_byte_array()
}

/// a program and its witness from their consensus encodings
fn decode(program: &[u8], witness: &[u8]) -> Arc<RedeemNode> {
    RedeemNode::decode::<_, _, Elements>(
        BitIter::from(program.iter().copied()),
        BitIter::from(witness.iter().copied()),
    )
    .expect("decode")
}

/// the unpruned program with the witness bound: from .uprog (and .wnames beside it) + the witness spec,
/// or the .simpl text
fn program_with_witness(arg: &str, witness_path: &str) -> Arc<RedeemNode> {
    let witness = witness::load(witness_path);
    if !arg.ends_with(".uprog") {
        return parse_text(arg, &witness);
    }
    let p = std::fs::read(arg).unwrap();
    let names_path = format!("{}.wnames", arg.trim_end_matches(".uprog"));
    let names: Vec<String> =
        serde_json::from_str(&std::fs::read_to_string(&names_path).expect("the .wnames of the program")).unwrap();
    unique_names(&names);
    let mut wbytes = Vec::new();
    {
        let mut bw = BitWriter::new(&mut wbytes);
        for name in &names {
            // the values in the order the encoding reads them
            let v = witness
                .get(name.as_str())
                .unwrap_or_else(|| panic!("no value for witness node {}", name));
            simplicity::encode_value(v, &mut bw).unwrap();
        }
        bw.flush_all().unwrap();
    }
    decode(&p, &wbytes)
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

/// the outputs to dest are explicit: say so when dest is a confidential address, whose blinding key is not used
fn explicit_note(dest: &Address) {
    if dest.blinding_pubkey.is_some() {
        eprintln!(
            "note: {} is confidential, but the output to it is explicit: its amount and asset are public",
            dest
        );
    }
}

/// an explicit output of sats of asset
fn explicit_txout(asset: AssetId, sats: u64, script_pubkey: Script) -> TxOut {
    TxOut {
        asset: confidential::Asset::Explicit(asset),
        value: confidential::Value::Explicit(sats),
        nonce: confidential::Nonce::Null,
        script_pubkey,
        witness: TxOutWitness::default(),
    }
}

/// a transaction with one input, spending previous_output, and the outputs
fn tx_spending(previous_output: OutPoint, output: Vec<TxOut>) -> Transaction {
    Transaction {
        version: 2,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output,
            is_pegin: false,
            script_sig: Script::new(),
            sequence: Sequence::MAX,
            asset_issuance: AssetIssuance::default(),
            witness: TxInWitness::default(),
        }],
        output,
    }
}

struct Spend {
    tx: Transaction,
    utxo: TxOut,
    info: TaprootSpendInfo,
    script: Script,
}

impl Spend {
    fn control_block(&self) -> Vec<u8> {
        self.info
            .control_block(&(self.script.clone(), simplicity::leaf_version()))
            .unwrap()
            .serialize()
    }
}

/// the transaction spending <txid>:<vout> (sats of asset, held by the verifier's output) to dest minus the fee
fn spend_tx(cmr: &[u8; 32], internal_key: &str, network: &'static AddressParams, pos: &[String]) -> Spend {
    let txid = Txid::from_str(&pos[0]).expect("txid");
    let vout: u32 = pos[1].parse().expect("vout");
    let sats: u64 = pos[2].parse().expect("amount in satoshis");
    let asset = AssetId::from_str(&pos[3]).expect("asset id");
    let dest = Address::parse_with_params(&pos[4], network).expect("destination address");
    explicit_note(&dest);
    let fee: u64 = pos[5].parse().expect("fee in satoshis");
    let (info, script, key) = spend_info(cmr, internal_key);
    let secp_ctx = secp::Secp256k1::verification_only();
    let address = Address::p2tr(&secp_ctx, key, info.merkle_root(), None, network);
    let utxo = explicit_txout(asset, sats, address.script_pubkey());
    let paid = sats.checked_sub(fee).expect("the fee exceeds the amount");
    let tx = tx_spending(
        OutPoint { txid, vout },
        vec![
            explicit_txout(asset, paid, dest.script_pubkey()),
            TxOut::new_fee(fee, asset),
        ],
    );
    Spend { tx, utxo, info, script }
}

/// the Simplicity environment of input 0 of the spend
fn environment(spend: &Spend, cmr: &[u8; 32], genesis_hash: BlockHash) -> ElementsEnv<Arc<Transaction>> {
    let control = spend
        .info
        .control_block(&(spend.script.clone(), simplicity::leaf_version()))
        .unwrap();
    ElementsEnv::new(
        Arc::new(spend.tx.clone()),
        vec![ElementsUtxo::from(spend.utxo.clone())],
        0,
        Cmr::from_byte_array(*cmr),
        control,
        None,
        genesis_hash,
    )
}

/// each witness node once: a node that occurs twice could be given two values by a spender
fn unique_names(names: &[String]) {
    let mut seen = HashSet::new();
    for name in names {
        if !seen.insert(name) {
            fail(&format!("the witness node {} occurs twice", name));
        }
    }
}

fn compile(pos: &[String]) {
    let (node, names) = parse_commit(&pos[1]);
    unique_names(&names);
    let p = node.to_vec_without_witness();
    std::fs::write(format!("{}.uprog", pos[2]), &p).unwrap();
    std::fs::write(format!("{}.wnames", pos[2]), serde_json::to_string(&names).unwrap()).unwrap();
    println!(
        "{{\"cmr\":\"{}\",\"unpruned_bytes\":{},\"witness_nodes\":{}}}",
        hex(&node.cmr().to_byte_array()),
        p.len(),
        names.len()
    );
}

fn address(pos: &[String], internal_key: &str) {
    let cmr = program_cmr(&pos[1]);
    let network = params(&pos[2]);
    let (info, script, key) = spend_info(&cmr, internal_key);
    let secp_ctx = secp::Secp256k1::verification_only();
    let address = Address::p2tr(&secp_ctx, key, info.merkle_root(), None, network);
    let control = info
        .control_block(&(script, simplicity::leaf_version()))
        .unwrap()
        .serialize();
    println!(
        "{{\"cmr\":\"{}\",\"internal_key\":\"{}\",\"output_key\":\"{}\",\"address\":\"{}\",\"script_pubkey\":\"{}\",\"control_block\":\"{}\"}}",
        hex(&cmr),
        key,
        info.output_key().into_inner(),
        address,
        hex(address.script_pubkey().as_bytes()),
        hex(&control)
    );
}

fn sighash(pos: &[String], flags: &Flags, internal_key: &str) {
    let cmr = program_cmr(&pos[1]);
    let network = params(&pos[2]);
    let spend = spend_tx(&cmr, internal_key, network, &pos[3..]);
    let env = environment(&spend, &cmr, genesis(&pos[2], flags.get("genesis")));
    println!("{}", hex(env.c_tx_env().sighash_all().as_ref()));
}

fn spend(pos: &[String], flags: &Flags, internal_key: &str) {
    let network = params(&pos[3]);
    let t0 = std::time::Instant::now();
    let (p, w, cmr, bounds, executed) = if pos[1].ends_with(".prog") {
        // the pruned encodings saved by an earlier spend: decoded for the CMR and the cost, not executed
        let p = std::fs::read(&pos[1]).unwrap();
        let w = std::fs::read(&pos[2]).unwrap();
        let decoded = decode(&p, &w);
        (p, w, decoded.cmr().to_byte_array(), decoded.bounds(), false)
    } else {
        let unpruned = program_with_witness(&pos[1], &pos[2]);
        let cmr = unpruned.cmr().to_byte_array();
        eprintln!("program loaded in {:.1}s", t0.elapsed().as_secs_f64());
        let spend = spend_tx(&cmr, internal_key, network, &pos[4..]);
        let env = environment(&spend, &cmr, genesis(&pos[3], flags.get("genesis")));
        let program = unpruned
            .prune(&env)
            .expect("the program fails on this witness and transaction");
        if program.bounds().extra_cells > CELLS_MAX && !flags.contains_key("force") {
            // rust-simplicity's own cap is far larger, so this is checked before executing
            fail(&format!(
                "the program needs up to {} cells of the Bit Machine, above the consensus cap of {}",
                program.bounds().extra_cells,
                CELLS_MAX
            ));
        }
        let mut mac = BitMachine::for_program(&program).expect("machine");
        mac.exec(&program, &env).expect("the pruned program fails");
        let (p, w) = program.to_vec_with_witness();
        eprintln!("pruned and executed in {:.1}s", t0.elapsed().as_secs_f64());
        if let Some(out) = flags.get("save") {
            std::fs::write(format!("{}.prog", out), &p).unwrap();
            std::fs::write(format!("{}.wit", out), &w).unwrap();
        }
        (p, w, cmr, program.bounds(), true)
    };
    let mut spend = spend_tx(&cmr, internal_key, network, &pos[4..]);
    let stack = vec![w.clone(), p.clone(), cmr.to_vec(), spend.control_block()];
    // the budget as a node computes it: 1000 mWU per byte of the serialized witness stack, plus 50 bytes
    let stack_bytes = simplicity::elements::encode::serialize(&stack).len();
    let budget = (stack_bytes + 50) * 1000;
    let cost: u64 = bounds.cost.to_string().parse().unwrap();
    let covered = bounds.cost.is_budget_valid(&stack);
    spend.tx.input[0].witness.script_witness = Witness::from_slice(&stack);
    let weight = spend.tx.weight();
    eprintln!(
        "cost {} mWU, program {} bytes, witness {} bytes, witness stack {} bytes (budget {} mWU, covered: {}), cells {} (cap {}), tx weight {} WU",
        cost,
        p.len(),
        w.len(),
        stack_bytes,
        budget,
        covered,
        bounds.extra_cells,
        CELLS_MAX,
        weight
    );
    let mut refused = Vec::new();
    if bounds.extra_cells > CELLS_MAX {
        refused.push(format!("the program needs more than {} cells", CELLS_MAX));
    }
    if !covered {
        refused.push("the input's budget does not cover the cost".to_string());
    }
    if weight > STANDARD_WEIGHT {
        refused.push(format!(
            "the transaction weighs more than {} WU, which nodes do not relay",
            STANDARD_WEIGHT
        ));
    }
    if !executed {
        eprintln!("note: built from the saved .prog and .wit, which were not executed against this transaction");
    }
    if !refused.is_empty() {
        if !flags.contains_key("force") {
            fail(&format!(
                "{} (--force prints the transaction anyway)",
                refused.join("; ")
            ));
        }
        eprintln!("--force: {}", refused.join("; "));
    }
    println!("{}", serialize_hex(&spend.tx));
}

fn wallet(pos: &[String], flags: &Flags) {
    let network = params(&pos[1]);
    let secp_ctx = secp::Secp256k1::new();
    let pk = bitcoin::PublicKey::new(keypair(flags).public_key());
    let blinder = flags
        .get("blinding")
        .map(|bk| secp::PublicKey::from_secret_key(&secp_ctx, &secp::SecretKey::from_str(bk).expect("blinding key")));
    println!(
        "{{\"pubkey\":\"{}\",\"address\":\"{}\",\"confidential_address\":\"{}\"}}",
        pk,
        Address::p2wpkh(&pk, None, network),
        blinder
            .map(|b| Address::p2wpkh(&pk, Some(b), network).to_string())
            .unwrap_or_default()
    );
}

fn send(pos: &[String], flags: &Flags) {
    let network = params(&pos[1]);
    let secp_ctx = secp::Secp256k1::new();
    let keypair = keypair(flags);
    let pk = bitcoin::PublicKey::new(keypair.public_key());
    let funding_hex = std::fs::read_to_string(&pos[2]).unwrap();
    let funding: Transaction =
        simplicity::elements::encode::deserialize(&hex_to_bytes(funding_hex.trim())).expect("funding transaction hex");
    let vout: u32 = pos[3].parse().expect("vout");
    let utxo = funding.output[vout as usize].clone();
    assert_eq!(
        utxo.script_pubkey,
        Address::p2wpkh(&pk, None, network).script_pubkey(),
        "the output does not pay the key"
    );
    let dest = Address::parse_with_params(&pos[4], network).expect("destination address");
    explicit_note(&dest);
    let sats: u64 = pos[5].parse().expect("amount in satoshis");
    let fee: u64 = pos[6].parse().expect("fee in satoshis");
    // the input: explicit, or unblinded with the blinding key
    let secrets = match (utxo.value, utxo.asset) {
        (confidential::Value::Explicit(v), confidential::Asset::Explicit(a)) => TxOutSecrets::new(
            a,
            confidential::AssetBlindingFactor::zero(),
            v,
            confidential::ValueBlindingFactor::zero(),
        ),
        _ => {
            let blinding = flags
                .get("blinding")
                .expect("--blinding <hex> for a confidential input");
            utxo.unblind(&secp_ctx, secp::SecretKey::from_str(blinding).unwrap())
                .expect("unblind")
        }
    };
    let confidential = utxo.value.is_confidential();
    let change = sats
        .checked_add(fee)
        .and_then(|out| secrets.value.checked_sub(out))
        .expect("the input does not cover the amount and the fee");
    eprintln!(
        "input: {} sats of {}{}",
        secrets.value,
        secrets.asset,
        if confidential { " (confidential)" } else { "" }
    );
    let mut outputs = vec![explicit_txout(secrets.asset, sats, dest.script_pubkey())];
    if confidential || change > 0 {
        // a confidential input needs a confidential output for the blinders to balance: the change
        let change_addr = Address::parse_with_params(flags.get("change").expect("--change <address>"), network)
            .expect("change address");
        if confidential {
            let blinder = change_addr
                .blinding_pubkey
                .expect("the change address must be confidential");
            let (txout, _, _, _) = TxOut::new_last_confidential(
                &mut secp::rand::thread_rng(),
                &secp_ctx,
                change,
                secrets.asset,
                change_addr.script_pubkey(),
                blinder,
                &[secrets],
                &[],
            )
            .expect("blind the change");
            outputs.push(txout);
        } else {
            outputs.push(explicit_txout(secrets.asset, change, change_addr.script_pubkey()));
        }
    }
    outputs.push(TxOut::new_fee(fee, secrets.asset));
    let mut tx = tx_spending(
        OutPoint {
            txid: funding.txid(),
            vout,
        },
        outputs,
    );
    let script_code = Script::new_p2pkh(&pk.pubkey_hash());
    let sighash = SighashCache::new(&tx).segwitv0_sighash(0, &script_code, utxo.value, EcdsaSighashType::All);
    let sig = secp_ctx.sign_ecdsa(
        &secp::Message::from_digest(sighash.to_byte_array()),
        &keypair.secret_key(),
    );
    let mut sig_bytes = sig.serialize_der().to_vec();
    sig_bytes.push(EcdsaSighashType::All as u8);
    tx.input[0].witness.script_witness = Witness::from_slice(&[sig_bytes, pk.to_bytes()]);
    eprintln!(
        "to {}: {} sats, change {} sats, fee {} sats, tx weight {} WU",
        pos[4],
        sats,
        change,
        fee,
        tx.weight()
    );
    println!("{}", serialize_hex(&tx));
}

fn keyspend(pos: &[String], flags: &Flags, internal_key: &str) {
    let cmr = program_cmr(&pos[1]);
    let network = params(&pos[2]);
    let secp_ctx = secp::Secp256k1::new();
    let keypair = keypair(flags);
    let (xonly, _) = keypair.x_only_public_key();
    let mut spend = spend_tx(&cmr, internal_key, network, &pos[3..]);
    let genesis_hash = genesis(&pos[2], flags.get("genesis"));
    let tweak = spend.info.tap_tweak().to_scalar();
    let tweaked = keypair.add_xonly_tweak(&secp_ctx, &tweak).expect("tweak");
    assert_eq!(
        tweaked.x_only_public_key().0,
        spend.info.output_key().into_inner(),
        "output key"
    );
    let sighash = SighashCache::new(&spend.tx)
        .taproot_key_spend_signature_hash(
            0,
            &Prevouts::All(&[spend.utxo.clone()]),
            SchnorrSighashType::Default,
            genesis_hash,
        )
        .expect("sighash");
    let sig = secp_ctx.sign_schnorr_no_aux_rand(&secp::Message::from_digest(sighash.to_byte_array()), &tweaked);
    spend.tx.input[0].witness.script_witness = Witness::from_slice(&[sig.as_ref().to_vec()]);
    eprintln!(
        "key path: internal key {}, output key {}, tx weight {} WU",
        xonly,
        spend.info.output_key().into_inner(),
        spend.tx.weight()
    );
    println!("{}", serialize_hex(&spend.tx));
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (pos, flags) = parse_args(&args);
    let key = internal_key(&flags);
    match pos.first().map(String::as_str).unwrap_or("") {
        "compile" => compile(&pos),
        "address" => address(&pos, &key),
        "sighash" if pos.get(1).map(String::as_str) == Some("dummy") => {
            println!("{}", hex(env::dummy().c_tx_env().sighash_all().as_ref()));
        }
        "sighash" => sighash(&pos, &flags, &key),
        "spend" => spend(&pos, &flags, &key),
        "keyspend" => keyspend(&pos, &flags, &key),
        "wallet" => wallet(&pos, &flags),
        "send" => send(&pos, &flags),
        _ => {
            eprintln!("{}", USAGE);
            std::process::exit(2);
        }
    }
}
