A challenge cannot be copied, so one draw cannot feed two consumers:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Challenge;
fn bad(c: Challenge<u8>) { let other = c.clone(); }
```

Accepting a challenge consumes it:

```compile_fail,E0382
use longfellow_zk::runtime::v2::transcript::{Bound, Challenge};
fn bad(t: &Bound<'_, ()>, c: Challenge<u8>) {
    let _ = t.accept(c);
    let _ = t.accept(c);
}
```

Only a transcript draw stamps a challenge:

```compile_fail,E0451
use longfellow_zk::runtime::v2::transcript::Challenge;
fn bad(c: Challenge<u8>) -> Challenge<u8> { Challenge { value: 1, ..c } }
```

Positive control: an accepted challenge yields its value.

```
use longfellow_zk::runtime::v2::transcript::{Bound, Challenge, StaleChallenge};
fn take(t: &Bound<'_, ()>, c: Challenge<u8>) -> Result<u8, StaleChallenge> { t.accept(c) }
```
