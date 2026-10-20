// hand: run a program of the Python generators the way a node would, and measure it.
//
//   hand <program.simpl> <witness.json> [<witness.json> ...]
//
// The program (human-readable encoding) is parsed once; for every witness file it is pruned against
// the dummy transaction environment and executed, serialised to the consensus encoding, decoded again,
// executed again (the decoded program is what a node sees: its types, hence its cost, can differ from
// the generator's), and one JSON line is printed:
//   {"ok": true, "cost": <mWU of the decoded program>, "cost_pre_decode": ..., "program_bytes": ...,
//    "witness_bytes": ..., "cells": ..., "frames": ..., "cmr": "..."}
// or {"ok": false, "stage": "parse" | "finalize" | "machine" | "exec" | "decode" | "exec2", "error": "..."}.
// The cost is the static bound of the pruned program; cells and frames are the Bit Machine memory
// bounds (consensus caps the cells at 5,242,880).
use groth_harness::{env, witness};
use simplicity::human_encoding::Forest;
use simplicity::jet::Elements;
use simplicity::{BitIter, BitMachine, RedeemNode};
use std::collections::HashMap;
use std::sync::Arc;

struct Report {
    cost: u64,
    cost_pre_decode: u64,
    program_bytes: usize,
    witness_bytes: usize,
    cells: usize,
    frames: usize,
    cmr: String,
}

fn run(forest: &Forest, witness: &HashMap<Arc<str>, simplicity::Value>) -> Result<Report, (&'static str, String)> {
    let dummy = env::dummy();
    simplicity::types::Context::with_context(|ctx| {
        let node = forest
            .to_witness_node(&ctx, witness)
            .ok_or(("parse", "no main".to_string()))?;
        let program = node.finalize_pruned(&dummy).map_err(|e| ("finalize", e.to_string()))?;
        let mut mac = BitMachine::for_program(&program).map_err(|e| ("machine", e.to_string()))?;
        mac.exec(&program, &dummy).map_err(|e| ("exec", e.to_string()))?;
        let (p, w) = program.to_vec_with_witness();
        let decoded =
            RedeemNode::decode::<_, _, Elements>(BitIter::from(p.iter().cloned()), BitIter::from(w.iter().cloned()))
                .map_err(|e| ("decode", e.to_string()))?;
        assert_eq!(decoded.cmr(), program.cmr(), "CMR changed by the round trip");
        let mut mac = BitMachine::for_program(&decoded).map_err(|e| ("machine", e.to_string()))?;
        mac.exec(&decoded, &dummy).map_err(|e| ("exec2", e.to_string()))?;
        let bounds = decoded.bounds();
        Ok(Report {
            cost: bounds.cost.to_string().parse().unwrap(),
            cost_pre_decode: program.bounds().cost.to_string().parse().unwrap(),
            program_bytes: p.len(),
            witness_bytes: w.len(),
            cells: bounds.extra_cells,
            frames: bounds.extra_frames,
            cmr: program.cmr().to_string(),
        })
    })
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: hand <program.simpl> <witness.json> [<witness.json> ...]");
        std::process::exit(2);
    }
    let text = std::fs::read_to_string(&args[0]).unwrap();
    let forest = match Forest::parse::<Elements>(&text) {
        Ok(f) => f,
        Err(e) => {
            println!("{{\"ok\":false,\"stage\":\"parse\",\"error\":{:?}}}", e.to_string());
            return;
        }
    };
    for path in &args[1..] {
        match run(&forest, &witness::load(path)) {
            Ok(r) => println!(
                "{{\"ok\":true,\"cost\":{},\"cost_pre_decode\":{},\"program_bytes\":{},\"witness_bytes\":{},\"cells\":{},\"frames\":{},\"cmr\":\"{}\"}}",
                r.cost, r.cost_pre_decode, r.program_bytes, r.witness_bytes, r.cells, r.frames, r.cmr
            ),
            Err((stage, error)) => println!("{{\"ok\":false,\"stage\":\"{}\",\"error\":{:?}}}", stage, error),
        }
    }
}
