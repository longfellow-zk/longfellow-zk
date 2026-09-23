# Test Vectors {#test-vectors}

This section contains test vectors. Each test vector in specifies the configuration information and inputs. All values are encoded in hexadecimal strings.

## Test Vectors for Merkle Tree

These vectors exercise the tree construction and the batch inclusion
proof only.  The leaves below are the leaf digests themselves, so no
nonces are involved; the nonce-blinded leaf construction used by the
Ligero commitment is exercised by the vectors in
(#test-vectors-for-explicit-circuit-sumcheck-and-ligero), which list
their nonces explicitly.

### Vector 1

- Leaves:
  4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a
  dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986
  084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5
  e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71
  e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db
- Root: f22f4501ffd3bdffcecc9e4cd6828a4479aeedd6aa484eb7c1f808ccf71c6e76
- Proof for leaves (0,1): 
  084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5
  f03808f5b8088c61286d505e8e93aa378991d9889ae2d874433ca06acabcd493
- Proof for leaves (1,3):
  e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db
  084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5
  4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a

## Test Vectors for Fiat-Shamir

Let `p=115792089237316195423570985008687907853269984665640564039457584007908834671663` and `Fp` be the 4-word field defined by `p`.

### Vector 1: WriteBytes

- Description: Using `Fp`, the test steps are to (a) initialize the transcript object with the 4-byte string `test`; (b) write an array of bytes of size 100 that contains the integers 0, 1, 2, ..., 99;  (c) generate 16 field elements:
  - 0x8b297f0bffd583c6c6b6796385d5fd20a08665733b833970ebdd1054bbbc1b14
  - 0x0667c08ad7f38efec5f30dc8aa4f20d749cdcf96d63a770f9810ac5c0ca8dcb1
  - 0xc8037fc12d4da00b5dc7597e3042f33f72a06f970cb71fb6b103ebb5419d8a6b
  - 0xfbbcfa1eac48728fbfdacc1c21e2f78119457e0846337e46140e38e62856c4c5
  - 0x5358ae603691cc759faeb572fb6642654ea1c3dbc8f81d00276dd8c4df95aa58
  - 0x5266158c3c895dede5a23b6ce85a9f564b8059ebfcd1741f54497ec58189873e
  - 0x3ecea4b2343c007fc32f2aff40dc7320945f101ecae5d52494db21ad326e9739
  - 0x6462dd575e6b874118607212feec7ce5417ae3bf0f2e86604596f35d48bbaea2
  - 0x6d56c703c369edea3595db6b958241580ae9b4a76fead961413ed9e9e5852dcd
  - 0x6d31073cee650212a71b7b13e9f951e00ef3b14a008a79dd95047b26a4a83d06
  - 0x1b9e2a6666da63c43e52227d91a8a7f0bd5311f63c2e3a18839133375639e6cb
  - 0x332ea49dd23dd4745631ecbb15696192b1fa127256baf7a0483fd27db6f09a48
  - 0x43e735927ccbdc4d5ce912675d638d6d3dc8eef3def34504304e938846f157d6
  - 0xdc4a8868ae75e733a7257a8589230392a98d78594836dfccd01304742b5b3ad5
  - 0x976353931711c634f2691e507b119fd7f6e653d419a2620676122db08db18765
  - 0x332729ab436dca654866a9382deaee0add6fb7e90a80261f1488e56598e8bc99

### Vector 2: WriteFieldElement

- Starting from the state at the end of Vector 1,
  (a) write the field element '7' in Fp;
  (b) generate 16 field elements

  - 0x609db3e9a8f548df038519fa46cef23eb8c6553d3c1f698604e60a51613a738e
  - 0x1cb69cb31999eb88e83c7586aac53f5e3286b084b0cf9e43619b48df01e0a310
  - 0x3bf36e3ddc690a1b12b417628c115959b373d056c90c42dc2417baf46f538868
  - 0xe336594f29dcda52e48896517b5cdb2d062ffd861ab02db5f8ca197aacc635f6
  - 0xc1f396a8bad16bb0f57da6d380402a25b571bd4691226d11449a741440e325c8
  - 0x5195336ec73751de066e3a8939b40c3c5555f1a513486dfc50dcf4c2d47e6ff2
  - 0x8dcf872f3ded2b7ed1d1ee9a2b125bedc6eacd3c09b3a4a5286d8fc2fc3a6634
  - 0x950dd2ef7be25eab686a6688497962ee4ad521da12b9ff3d8e56ad9435885b12
  - 0xe14389d1d8448678cac33fdbc9aab20dba019e75149d170dd2f353891cd4b84f
  - 0xe84906c09cd6423865baf64e48027cc598d52bdb90b17524c87ea892e53b5200
  - 0x493cea587f1ec5622c04221cd6e5a41c26c1c1c24c0375f7aaa367d9678d83bc
  - 0x5aca0010aced30bcb3b84a7f10ea39c4269ab7c92fcb6cff52958d8921ef2cc5
  - 0x4498fa8340f41467c0fa813bd0ca83ef6e1c4b85c7b1168a94339fd9e8296139
  - 0xf9a95b738a8e775421b1baa503abbeed2d283b236ebba25e1954b3c993d30a3d
  - 0x98178711d03a0b1204ebb56b37bd3a2724dfb08e4dc925609391768b126d21f2
  - 0x79251f49534f5c4b10b798b2dbf6e80a3b07593f616ce6a9617ccc61040aac78

### Vector 3: WriteFieldElementArray

- Starting from the state at the end of Vector 2,
  (a) write the 2-long array of field elements `[8, 9]`;
  (b) generate 16 field elements:

```
0xae1a921288590205fc24543303ff527476359b8db4a983b2886a133b02f3217e
0x8c5d52a04b295f9fdb45ab66100fa00ca32c9634aa87cbbdb2bc3e1912459feb
0x12f82963b5b242156f6e9eb756eddee7652b60c7d6394403f7bd995e0b9bcd9c
0x880aa50b049b3939055deb7933749d338bb3fb5f64a9adf95019e6cfc232995c
0xf8558f693f0fa6df20a37147a898fb4c678831f566d80113bbe2cdcd18285da2
0xbbcc8d9b46f88bc8c6cec0ad2d5e49508b7db91d548548eddc61800de1329e1c
0x479a17244398caae8155a73438a22583df7de10a8a2e12ad53ddd3bc7305fac9
0x9ba1917f1227932250288a843f64b4e7b7f47a5fbc16c111f6e1f76235ccf38c
0xd1582138045d1636fb7f677c9e8a4a4143ce2b2bb54fb4f49fb0ad1fee5df6b4
0x05331e5b8508f79c017a8dfbbb805f3f8c5e3e4bc417e44849b9212439646331
0xb6b95862194ca52dcaa9ee651b7fc5b708f43feae108bb9a7f95213f4d069048
0xe86b1602f0a54c4e237867ebaf05e7581464fd238e50f6ed9c3cea63909c8e60
0xb7280439f3b21b113ff29cefe39292d5e2d137709c3d3cec36473a0f97a24e62
0xbeaa5e08257d232506fb3e46c6daa29e0859c34c7d0cd673bc6706ee261ae059
0x0691ead55728cd087a1952b22b6628ba4e26fbefc8debeec5e6fbc3a16f637be
0x47dc31f6d8bc9c44290781176df3e4b95ac8793a4a42fa5859c564d92d6d5af5
```

### Vector 4: Nat

- Starting from the state at the end of Vector 3,
  - (a) write the 4-byte string "nats";
  - (b) call `nat(n)` with the following list of parameters:
    - `[1, 1, 1, 2, 2, 2, 7, 7, 7, 7, 32, 32, 32, 32, 256, 256, 256, 256, 1000, 10000, 60000, 65535, 100000, 100000]`.
  - The result of each call corresponds to:
    - `[0, 0, 0, 0, 0, 0, 3, 0, 4, 5, 10, 30, 27, 22, 100, 189, 3, 92, 999, 3105, 40886, 51590, 56367, 10678]`

### Vector 5: Choice

- Starting from the state at the end of Vector 4, (a) write the 6-byte string "choose"; (b) call `choose(m, 20)` for the following values of `m`:
  - `m=31, k=20`: `[10, 29, 30, 11, 4, 15, 16, 28, 19, 21, 25, 18, 17, 3, 5, 23, 24, 22, 6, 1]`
  - `m=32, k=20`: `[3, 17, 18, 8, 30, 7, 14, 19, 25, 23, 12, 4, 31, 16, 0, 6, 20, 27, 11, 10]`
  - `m=63, k=20`: `[9, 56, 61, 45, 35, 53, 51, 3, 39, 32, 31, 6, 59, 58, 54, 22, 27, 62, 55, 19]`
  - `m=64, k=20`: `[12, 52, 39, 17, 51, 38, 58, 2, 28, 27, 46, 63, 61, 50, 40, 55, 47, 13, 56, 32]`
  - `m=1000, k=20`: `[157, 668, 572, 138, 913, 994, 797, 249, 440, 723, 489, 241, 383, 108, 710, 341, 406, 585, 42, 692]`
  - `m=65535, k=20`: `[40745, 48408, 17108, 44500, 53993, 10008, 24910, 52200, 61265, 54989, 41237, 25958, 28697, 61187, 34729, 3525, 9005, 38627, 9724, 12169]`

## Test Vectors for Explicit Circuit, Sumcheck, and Ligero {#test-vectors-for-explicit-circuit-sumcheck-and-ligero}

The following test vectors verify the complete zero-knowledge proof system using explicitly constructed layered quadratic circuits without requiring external binary circuit files or formats.

### Randomness used by these vectors

A Ligero commitment consumes randomness for the three blinding rows,
for the `NREQ` random elements that prefix every witness and quadratic
row, and for the Merkle leaf nonces.  A proof is therefore reproducible
only with respect to a fixed source of randomness.  Both vectors below
draw from the following deterministic generator, seeded with `12345`,
which is defined for test purposes only and **MUST NOT** be used to
produce real proofs:

```rust
pub struct SimpleRng {
    pub state: u64,
}

impl Rng for SimpleRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(len);
        let mut state = self.state;
        for _ in 0..len {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            out.push(((state >> 32) & 0xff) as u8);
        }
        self.state = state;
        out
    }
}
```

The `NREQ` Merkle nonces of the opened columns are reproduced below for
each vector, so that an implementation can check its commitment
independently of the generator above.  They also appear verbatim in the
complete proof serialization, immediately after the four response
polynomials and immediately before the run-length coded columns.

### Vector 1: $s$-gonal Circuit over P-256 (Field ID 2)

- **Description**: Circuit $C(n, m, s) = 0 \iff (s - 2)m^2 - (s - 4)m - 2n = 0$ verifying that $n$ is the $m$-th $s$-gonal polygonal number over the NIST P-256 scalar field $\mathbb{F}_p$.
- **Field**: P-256 Scalar Field (Field ID 2, order $p = 115792089210356248762697446949407573530086143415290314195533631308867097853951$)
- **Witness Inputs**: $W = [w_0, w_1, w_2, w_3] = [1, 45, 5, 6]$ with public input $w_0 = 1$, and private inputs $n = 45$, $m = 5$, $s = 6$.
- **Explicit Circuit Definition**:
  - **Inputs**: $N_{in} = 4$, $N_{pub} = 1$.
  - **Layer 1** (Intermediate wires $U = [u_0, u_1, u_2, u_3, u_4]$ from input $W$):
    - $u_0 = 1 = w_0 \cdot w_0$
    - $u_1 = m^2 = w_2 \cdot w_2$
    - $u_2 = s - 2 = w_3 \cdot w_0 - 2 \cdot w_0 \cdot w_0$
    - $u_3 = (s - 4)m = w_3 \cdot w_2 - 4 \cdot w_0 \cdot w_2$
    - $u_4 = 2n = 2 \cdot w_0 \cdot w_1$
  - **Layer 0** (Output wire $y_0 = 0$ from intermediate $U$):
    - $y_0 = u_2 \cdot u_1 - u_3 \cdot u_0 - u_4 \cdot u_0 = (s-2)m^2 - (s-4)m - 2n = 0$
- **Proof System Parameters**:
  - `RATE_INV`: 4 ($\rho = 1/4$)
  - `NREQ`: 6 (query count)
  - `NCOL`: 64 (encoded codeword length)
  - Derived geometry: `BLOCK` = 10, `DBLOCK` = 19, `WR` = 4, `NW` = 29,
    `NQ` = 2, `NWROW` = 8, `NQT` = 1, `NROW` = 14
- **Statement hash**: the 23-byte ASCII string `sgonal_test_vector_p256`
- **RNG seed**: 12345
- **Merkle nonces** (one per opened column, in the order the columns
  were chosen):
  - `d406ef8c46fd239545520a5363d67d61bad1750d37b087c1e3611a12d47e477f`
  - `5fe986cae604828cae4bfbbc7415d64cd5e755848755a0d9d3120ad46eea8d86`
  - `0fa8593d45fef897767ce05ec5feac76d8f21910bc0ada856aeaa777629048ef`
  - `63619b9a06c668a2414e46f859a2fdb1ba63e8718fa6ce4bf532b2fb0b8ff4ef`
  - `c9e35514c0ff4b62cb9730116947bef69325f3a4c1c6553b7bd161754f8008d8`
  - `057ec47e747c61954419b634dec16eb6adfeafb1a0e9fafbb2a9c85fcf9bced4`
- **Commitment Root**:
  `803aba51698a4bc4dddaa74b1d9971b8ec7c49c4847a7ff18e41dd476edf9b04`
- **Sumcheck Proof Size**: 768 bytes
- **Sumcheck Proof (hex)**:

    <{{test-vector1-sumcheck.txt}}

- **Ligero Proof Size**: 4652 bytes
- **Total ZK Proof Size**: 5452 bytes
- **Complete Proof Serialization (hex)**:

    <{{test-vector1-proof.txt}}

### Vector 2: Quadratic Polynomial Circuit over GF(2^128) (Field ID 5)

- **Description**: Circuit verifying $(s + 1)m^2 + (s + 1)m + n = 0$ over the binary field $GF(2^{128})$.
- **Field**: $GF(2^{128})$ (Field ID 5, polynomial representation modulo $x^{128} + x^7 + x^2 + x + 1$)
- **Witness Inputs**: $W = [w_0, w_1, w_2, w_3] = [1, 84, 5, 6]$ with public input $w_0 = 1$, and private inputs $n = 84$, $m = 5$, $s = 6$.
- **Explicit Circuit Definition**:
  - **Inputs**: $N_{in} = 4$, $N_{pub} = 1$.
  - **Layer 1** (Intermediate wires $U = [u_0, u_1, u_2, u_3, u_4]$):
    - $u_0 = 1 = w_0 \cdot w_0$
    - $u_1 = m^2 = w_2 \cdot w_2$
    - $u_2 = s + 1 = w_3 \cdot w_0 + w_0 \cdot w_0$
    - $u_3 = (s + 1)m = w_3 \cdot w_2 + w_0 \cdot w_2$
    - $u_4 = n = w_0 \cdot w_1$
  - **Layer 0** (Output wire $y_0 = 0$):
    - $y_0 = u_2 \cdot u_1 + u_3 \cdot u_0 + u_4 \cdot u_0 = (s+1)m^2 + (s+1)m + n = 0$
- **Proof System Parameters**:
  - `RATE_INV`: 4 ($\rho = 1/4$)
  - `NREQ`: 6 (query count)
  - `NCOL`: 64 (encoded codeword length)
  - Derived geometry: `BLOCK` = 10, `DBLOCK` = 19, `WR` = 4, `NW` = 29,
    `NQ` = 2, `NWROW` = 8, `NQT` = 1, `NROW` = 14
- **Statement hash**: the 26-byte ASCII string `sgonal_test_vector_gf2_128`
- **RNG seed**: 12345
- **Merkle nonces** (one per opened column, in the order the columns
  were chosen):
  - `7ef857289b65bef3539deca0df3f44c67bd0f86b02afddd2eaf2df6b9ba36497`
  - `33946263e6da1ec940a9047547a6296f465821313eeb867d988aed265b82eb53`
  - `87b402da5412750ec00175350a9579b1f458b668155ba582d31b5d71331f2d41`
  - `978ee556b7e529dea3e0fbbde3d83fcb11871c478dd3ddb15fc27e628487950e`
  - `1c320449d0bed51ad492d371d066d55c4db059a1c59c267094ae3087746b1e61`
  - `c809ce332b7354d1e4b593f335d980dc1f0579e171a0bd092761a12006f3b544`
- **Commitment Root**:
  `30dafd53c4f2441bb8457cd84fa69b3a822fbda58a46527d5cec8ce1903bc504`
- **Sumcheck Proof Size**: 384 bytes
- **Sumcheck Proof (hex)**:
  
    <{{test-vector2-sumcheck.txt}}

- **Ligero Proof Size**: 2632 bytes
- **Total ZK Proof Size**: 3048 bytes
- **Complete Proof Serialization (hex)**:

    <{{test-vector2-proof.txt}}
