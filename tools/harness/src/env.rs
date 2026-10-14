//! The dummy transaction environment the tests run in (the same one as SimplicityHL's `dummy_env`, so
//! that its sig_all_hash is a fixed constant): one input, one output, a zero CMR and genesis hash.
use simplicity::elements::taproot::ControlBlock;
use simplicity::elements::{self, confidential, AssetIssuance, BlockHash};
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicity::Cmr;
use std::sync::Arc;

pub fn dummy() -> ElementsEnv<Arc<elements::Transaction>> {
    let tx = elements::Transaction {
        version: 2,
        lock_time: elements::LockTime::ZERO,
        input: vec![elements::TxIn {
            previous_output: elements::OutPoint::default(),
            is_pegin: false,
            script_sig: elements::Script::new(),
            sequence: elements::Sequence::MAX,
            asset_issuance: AssetIssuance::default(),
            witness: elements::TxInWitness::default(),
        }],
        output: vec![elements::TxOut {
            asset: confidential::Asset::default(),
            value: confidential::Value::default(),
            nonce: confidential::Nonce::default(),
            script_pubkey: elements::Script::default(),
            witness: elements::TxOutWitness::default(),
        }],
    };
    let ctrl_blk: [u8; 33] = [
        0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff, 0x47, 0x33, 0x2f,
        0xb7, 0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52, 0x26, 0xd3, 0xbc, 0x09, 0xfc,
    ];
    let utxo = ElementsUtxo {
        script_pubkey: elements::Script::default(),
        asset: confidential::Asset::default(),
        value: confidential::Value::default(),
    };
    ElementsEnv::new(
        Arc::new(tx),
        vec![utxo],
        0,
        Cmr::from_byte_array([0; 32]),
        ControlBlock::from_slice(&ctrl_blk).unwrap(),
        None,
        BlockHash::from_byte_array([0; 32]),
    )
}
