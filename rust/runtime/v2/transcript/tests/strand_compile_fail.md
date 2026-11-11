Absorbing strands cannot produce challenges before their transition:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(mut s: Strand) { s.next_block(); }
```

A PRF cannot absorb messages or produce a continuation:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Prf;
fn bad(mut p: Prf) { p.write(b"late"); }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Prf;
fn bad(p: Prf) { p.continue_strand(); }
```

Both finalization and continuation consume their absorbing strand:

```compile_fail,E0382
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(s: Strand) { let _ = s.end_strand(); let _ = s.end_strand(); }
```

```compile_fail,E0382
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(s: Strand) { let _ = s.continue_strand(); let _ = s.continue_strand(); }
```

State access, id replacement and cloning are unavailable:

```compile_fail,E0616
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(s: Strand) { let _ = s.hash; }
```

```compile_fail,E0616
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(mut s: Strand) { s.id = 0; }
```

```compile_fail,E0616
use longfellow_zk::runtime::v2::transcript::Prf;
fn bad(p: Prf) { let _ = p.parent; }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Strand;
fn bad(s: Strand) { let _ = s.clone(); }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Prf;
fn bad(p: Prf) { let _ = p.clone(); }
```

The permitted transitions compose without exposing a digest:

```
use longfellow_zk::runtime::v2::transcript::Strand;
let mut root = Strand::new();
root.write(b"context");
let (mut challenges, mut next) = root.continue_strand();
let challenge = challenges.next_block();
next.write(b"next message");
let _ = (challenge, next.end_strand().next_block());
```
