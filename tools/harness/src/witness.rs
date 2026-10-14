//! Witness files: JSON specs of Simplicity values, written by the Python generators (groth/dsl.py).
//!
//! A file maps witness node names to values, `{"w_in": VALUE}`, where VALUE is one of
//!   {"w": "<hex>"}              a word of 4 * len(hex) bits (a power of two)
//!   {"bit": 0|1}                a bit (the type 2)
//!   {"p": [VALUE, VALUE]}       a pair
//!   {"none": TYPE}              the left injection of unit into 1 + TYPE
//!   {"some": VALUE}             the right injection into 1 + type(VALUE)
//!   {"l": VALUE, "t": TYPE}     the left injection into type(VALUE) + TYPE
//!   {"r": VALUE, "t": TYPE}     the right injection into TYPE + type(VALUE)
//! and TYPE is {"w": bits}, {"p": [TYPE, TYPE]} or {"opt": TYPE}.
use simplicity::types::Final;
use simplicity::Value;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

pub fn hex_to_bytes(h: &str) -> Vec<u8> {
    (0..h.len()).step_by(2).map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap()).collect()
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// a word value from its hex digits: bytes paired up into a balanced tree
fn word(hex: &str) -> Value {
    let bits = hex.len() * 4;
    assert!(bits.is_power_of_two(), "word width must be a power of two: {} bits", bits);
    if bits < 8 {
        let v = u8::from_str_radix(hex, 16).unwrap();
        return match bits {
            1 => Value::u1(v),
            2 => Value::u2(v),
            4 => Value::u4(v),
            _ => unreachable!(),
        };
    }
    let mut vals: VecDeque<Value> = hex_to_bytes(hex).into_iter().map(Value::u8).collect();
    while vals.len() > 1 {
        let mut next = VecDeque::new();
        while let (Some(a), Some(b)) = (vals.pop_front(), vals.pop_front()) {
            next.push_back(Value::product(a, b));
        }
        vals = next;
    }
    vals.pop_front().unwrap()
}

fn ty(spec: &serde_json::Value) -> Arc<Final> {
    let o = spec.as_object().unwrap();
    if let Some(b) = o.get("w") {
        let bits = b.as_u64().unwrap() as usize;
        Final::two_two_n(bits.trailing_zeros() as usize).unwrap()
    } else if let Some(p) = o.get("p") {
        Final::product(ty(&p[0]), ty(&p[1]))
    } else if let Some(t) = o.get("opt") {
        Final::sum(Final::unit(), ty(t))
    } else {
        panic!("bad type spec {}", spec)
    }
}

pub fn value(spec: &serde_json::Value) -> Value {
    let o = spec.as_object().unwrap();
    if let Some(h) = o.get("w") {
        word(h.as_str().unwrap())
    } else if let Some(b) = o.get("bit") {
        Value::u1(b.as_u64().unwrap() as u8)
    } else if let Some(p) = o.get("p") {
        Value::product(value(&p[0]), value(&p[1]))
    } else if let Some(t) = o.get("none") {
        Value::none(ty(t))
    } else if let Some(v) = o.get("some") {
        Value::some(value(v))
    } else if let Some(v) = o.get("l") {
        Value::left(value(v), ty(o.get("t").expect("l needs t")))
    } else if let Some(v) = o.get("r") {
        Value::right(ty(o.get("t").expect("r needs t")), value(v))
    } else {
        panic!("bad value spec {}", spec)
    }
}

/// the witness map of a file
pub fn load(path: &str) -> HashMap<Arc<str>, Value> {
    let spec: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    spec.as_object().unwrap().iter().map(|(k, v)| (Arc::from(k.as_str()), value(v))).collect()
}

/// the single value of a file with one witness node
pub fn load_single(path: &str) -> Value {
    let map = load(path);
    assert_eq!(map.len(), 1, "one witness node expected in {}", path);
    map.into_values().next().unwrap()
}
