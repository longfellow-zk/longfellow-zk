import LfzkV2.Current.CanonicalPrefix

/-! The public request a proof answers: the session, the hash circuit's
public presentation bits and the signature circuit's public inputs. It is
application data, independent of the transcript format that absorbs it. -/
namespace LfzkV2.Current

structure PublicRequest (publicCount primeCount : ℕ) (Prime : Type) where
  session : BoundedBytes CanonicalPrefix.maxLength
  publicBits : Fin publicCount → Bool
  primeInputs : Fin primeCount → Prime

end LfzkV2.Current
