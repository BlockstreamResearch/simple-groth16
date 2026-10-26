#!/usr/bin/env node
// snarkjs 0.7.6's fflonk prover and verifier with a SHA-256 Fiat-Shamir transcript instead of Keccak-256.
// The transcript is otherwise snarkjs's: the same items in the same order, points uncompressed (x then y,
// 32 bytes each, big-endian), scalars 32 bytes big-endian, and each challenge the digest as a big-endian
// integer reduced mod r.  The verifier's SHA-256 mode (groth/fflonk/verifier.py) checks these proofs.
//
//   node tools/snarkjs_sha256.mjs prove <circuit.zkey> <witness.wtns> <proof.json> <public.json>
//   node tools/snarkjs_sha256.mjs verify <verification_key.json> <public.json> <proof.json>
//
// On each run it copies snarkjs's src/ afresh to src-sha256/ inside the snarkjs package ($NODE_MODULES/snarkjs),
// with Keccak256Transcript.js hashing with SHA-256 (the class keeps its name, so nothing else changes), and
// runs fflonk_prove / fflonk_verify from the copy.  The
// setup and the verification key are snarkjs's own: the transcript does not enter them.
// NODE_MODULES: the node_modules that holds snarkjs 0.7.6 (default: circuits/node_modules).
import fs from 'fs';
import path from 'path';
import { fileURLToPath, pathToFileURL } from 'url';

const ROOT = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const NODE_MODULES = process.env.NODE_MODULES || path.join(ROOT, 'circuits', 'node_modules');
const SNARKJS = path.join(NODE_MODULES, 'snarkjs');
const VERSION = '0.7.6';
const KECCAK = 'import {keccak_256} from "@noble/hashes/sha3";';
const SHA256 = 'import {sha256 as keccak_256} from "@noble/hashes/sha256"; // the SHA-256 transcript';

function prepare() {
    const pkg = JSON.parse(fs.readFileSync(path.join(SNARKJS, 'package.json'), 'utf8'));
    if (pkg.version !== VERSION) {
        throw new Error(`snarkjs ${pkg.version} in ${NODE_MODULES}: the patch is written for ${VERSION}`);
    }
    const dst = path.join(SNARKJS, 'src-sha256');
    fs.rmSync(dst, { recursive: true, force: true });
    fs.cpSync(path.join(SNARKJS, 'src'), dst, { recursive: true });
    const file = path.join(dst, 'Keccak256Transcript.js');
    const src = fs.readFileSync(file, 'utf8');
    if (src.split(KECCAK).length !== 2) {
        throw new Error(`${file}: the Keccak import to replace is not there exactly once`);
    }
    fs.writeFileSync(file, src.replace(KECCAK, SHA256));
    return dst;
}

// JSON with bigints as decimal strings, as snarkjs writes it (stringifyBigInts)
function stringify(v) {
    if (typeof v === 'bigint') return v.toString();
    if (Array.isArray(v)) return v.map(stringify);
    if (v !== null && typeof v === 'object') return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, stringify(x)]));
    return v;
}

const quiet = { debug() {}, info() {}, warn: console.warn, error: console.error };

async function main() {
    const [cmd, ...args] = process.argv.slice(2);
    const dir = prepare();
    const load = async (name) => (await import(pathToFileURL(path.join(dir, name)).href)).default;
    if (cmd === 'prove' && args.length === 4) {
        const [zkey, wtns, proofFile, publicFile] = args;
        const prove = await load('fflonk_prove.js');
        const { proof, publicSignals } = await prove(zkey, wtns, quiet);
        fs.writeFileSync(proofFile, JSON.stringify(stringify(proof), null, 1));
        fs.writeFileSync(publicFile, JSON.stringify(stringify(publicSignals), null, 1));
        console.log(`proof (SHA-256 transcript) written to ${proofFile}`);
    } else if (cmd === 'verify' && args.length === 3) {
        const [vkFile, publicFile, proofFile] = args;
        const read = (f) => JSON.parse(fs.readFileSync(f, 'utf8'));
        const verify = await load('fflonk_verify.js');
        const ok = await verify(read(vkFile), read(publicFile), read(proofFile), quiet);
        console.log(ok ? 'PROOF VERIFIED (SHA-256 transcript)' : 'INVALID PROOF (SHA-256 transcript)');
        process.exitCode = ok ? 0 : 1;
    } else {
        console.error('usage: snarkjs_sha256.mjs prove <zkey> <wtns> <proof.json> <public.json>');
        console.error('       snarkjs_sha256.mjs verify <verification_key.json> <public.json> <proof.json>');
        process.exitCode = 2;
    }
}

main().then(() => process.exit(process.exitCode || 0), (err) => {
    console.error(err);
    process.exit(1);
});
