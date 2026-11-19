A component reads only parts of the statement its session opened with.
Binding an arbitrary value is crate-private: a session opened with a
statement cannot be bound to an unrelated value, and a bound part cannot be
projected to one. The joint drivers that bind frontends are crate-private.
Statement types expose named accessors instead (`Opened::geometry`).

```compile_fail,E0624
use longfellow_zk::runtime::v2::transcript::{Bound, Opened, ZkStatement};
fn bad<'a>(s: &'a mut Opened<'_, ZkStatement<'_>>, other: &'static u64) -> Bound<'a, u64> {
    s.bound(|_| other)
}
```

```compile_fail,E0624
use longfellow_zk::runtime::v2::transcript::{Bound, Transcript};
fn bad<'a>(t: &'a mut Transcript, other: &'a u64) -> Bound<'a, u64> { t.bound(other) }
```

```compile_fail,E0624
use longfellow_zk::runtime::v2::transcript::Bound;
fn bad(b: &mut Bound<'_, u8>, other: &'static u64) { let _ = b.project(|_| other); }
```

The Polygero profile has one home, `JointGeometry`, written from the
geometry the proof is parsed and verified against; the identity message
cannot carry a second, unchecked copy:

```compile_fail,E0560
use longfellow_zk::runtime::v2::transcript::ZkStatement;
let _ = ZkStatement { context: b"context", profile: [0; 4] };
```
