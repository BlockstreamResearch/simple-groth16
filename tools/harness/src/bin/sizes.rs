// sizes: what the pruned program consists of, for one witness.
//
//   sizes <program.simpl> <witness.json> [name,name,...]
//
// Prunes the program as `hand` does and counts the shared nodes of the result by kind, the bits of its
// constants and the CMRs of its pruned branches (32 bytes each), next to the encoded size.  With a list
// of definition names, each node of the pruned program is attributed to the first of them that contains
// a node with its CMR (or to "rest"), and the bytes are estimated per name.
use groth_harness::{env, witness};
use simplicity::dag::{DagLike, MaxSharing};
use simplicity::human_encoding::Forest;
use simplicity::jet::Elements;
use simplicity::node::{Inner, Redeem};
use std::collections::{BTreeMap, HashMap};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(args.len() == 2 || args.len() == 3, "usage: sizes <program.simpl> <witness.json> [names]");
    let names: Vec<String> = args.get(2).map(|s| s.split(',').map(String::from).collect()).unwrap_or_default();
    let text = std::fs::read_to_string(&args[0]).unwrap();
    let forest = Forest::parse::<Elements>(&text).unwrap_or_else(|e| panic!("{}", e));
    let wit = witness::load(&args[1]);
    let dummy = env::dummy();
    simplicity::types::Context::with_context(|ctx| {
        let node = forest.to_witness_node(&ctx, &wit).expect("no main");
        let program = node.finalize_pruned(&dummy).expect("finalize");
        let (p, _) = program.to_vec_with_witness();
        let mut defs = HashMap::new();
        let main = forest.roots().get("main").expect("no main").clone();
        for item in main.post_order_iter::<MaxSharing<_>>() {
            defs.entry(item.node.name().to_string()).or_insert_with(|| item.node.clone());
        }
        let mut owner = HashMap::new();
        for (i, nm) in names.iter().enumerate() {
            let root = defs.get(nm.as_str()).unwrap_or_else(|| panic!("no definition {}", nm));
            for item in root.clone().post_order_iter::<MaxSharing<_>>() {
                owner.entry(item.node.cmr()).or_insert(i);
            }
        }
        let mut parts = vec![(0usize, 0usize, 0usize); names.len() + 1]; // nodes, word bits, hidden CMRs
        let mut kinds: BTreeMap<&str, usize> = BTreeMap::new();
        let (mut word_bits, mut hidden) = (0usize, 0usize);
        for item in program.post_order_iter::<MaxSharing<Redeem>>() {
            let part = &mut parts[*owner.get(&item.node.cmr()).unwrap_or(&names.len())];
            part.0 += 1;
            match item.node.inner() {
                Inner::AssertL(..) | Inner::AssertR(..) => part.2 += 1,
                Inner::Word(w) => part.1 += w.len(),
                _ => {}
            }
            let k = match item.node.inner() {
                Inner::Iden => "iden", Inner::Unit => "unit", Inner::InjL(_) | Inner::InjR(_) => "inj",
                Inner::Take(_) => "take", Inner::Drop(_) => "drop", Inner::Comp(..) => "comp",
                Inner::Case(..) => "case", Inner::AssertL(..) | Inner::AssertR(..) => { hidden += 1; "assert" }
                Inner::Pair(..) => "pair", Inner::Disconnect(..) => "disconnect", Inner::Witness(_) => "witness",
                Inner::Fail(_) => "fail", Inner::Jet(_) => "jet",
                Inner::Word(w) => { word_bits += w.len(); "word" }
            };
            *kinds.entry(k).or_insert(0) += 1;
        }
        let nodes: usize = kinds.values().sum();
        println!("program {} bytes, {} shared nodes", p.len(), nodes);
        for (k, n) in &kinds {
            println!("  {:10} {:7}", k, n);
        }
        println!("constants {} bytes, pruned-branch CMRs {} bytes, the rest {} bytes ({:.1} bits per node)",
                 word_bits / 8, hidden * 32, p.len() - word_bits / 8 - hidden * 32,
                 (p.len() * 8 - word_bits - hidden * 256) as f64 / nodes as f64);
        if !names.is_empty() {
            let per_node = (p.len() * 8 - word_bits - hidden * 256) as f64 / nodes as f64;
            for (i, (n, wb, h)) in parts.iter().enumerate() {
                let nm = names.get(i).map(|s| s.as_str()).unwrap_or("rest");
                println!("  {:12} {:6} nodes {:7} constant bytes {:5} CMR bytes  ~{:6.0} bytes",
                         nm, n, wb / 8, h * 32, (*n as f64 * per_node + (*wb + h * 256) as f64) / 8.0);
            }
        }
    });
}
