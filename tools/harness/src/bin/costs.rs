// costs: the static cost of every named definition of a program, as rust-simplicity counts it.
//
//   costs <program.simpl>
//
// Prints one "name cost" line per definition reachable from main, using the types inferred for main.
// The generators record their own estimate of each definition; comparing the two locates a cost
// model mismatch.
use simplicity::dag::{DagLike, NoSharing};
use simplicity::human_encoding::Forest;
use simplicity::jet::Elements;
use simplicity::node::Inner;
use std::collections::HashMap;

fn main() {
    let path = std::env::args().nth(1).expect("usage: costs <program.simpl>");
    let text = std::fs::read_to_string(&path).unwrap();
    let forest = Forest::parse::<Elements>(&text).unwrap_or_else(|e| panic!("{}", e));
    let main = forest.roots().get("main").expect("no main").clone();
    let mut cost: HashMap<*const _, u64> = HashMap::new();
    let mut seen: HashMap<String, u64> = HashMap::new();
    for item in main.post_order_iter::<NoSharing>() {
        let node = item.node;
        let w = |ty: &simplicity::types::Final| ty.bit_width() as u64;
        let child = |c: &std::sync::Arc<_>| cost[&std::sync::Arc::as_ptr(c)];
        let c = match node.inner() {
            Inner::Iden => 100 + w(&node.arrow().target),
            Inner::Unit => 100,
            Inner::InjL(c) | Inner::InjR(c) | Inner::Take(c) | Inner::Drop(c) => 100 + child(c),
            Inner::Comp(l, r) => 100 + w(&l.arrow().target) + child(l) + child(r),
            Inner::Case(l, r) => 100 + child(l).max(child(r)),
            Inner::AssertL(l, _) => 100 + child(l),
            Inner::AssertR(_, r) => 100 + child(r),
            Inner::Pair(l, r) => 100 + child(l) + child(r),
            Inner::Witness(_) => 100 + w(&node.arrow().target),
            Inner::Jet(j) => 100 + j.cost().to_string().parse::<u64>().unwrap(),
            Inner::Word(v) => 100 + v.len() as u64,
            Inner::Disconnect(..) | Inner::Fail(..) => panic!("unsupported node"),
        };
        cost.insert(std::sync::Arc::as_ptr(&node), c);
        seen.entry(node.name().to_string()).or_insert(c);
    }
    let mut names: Vec<_> = seen.into_iter().collect();
    names.sort();
    for (n, c) in names {
        println!("{} {}", n, c);
    }
}
