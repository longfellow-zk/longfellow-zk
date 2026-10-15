import Lfzk.TwoFieldV1Rows

/-!
# A satisfiable ideal-sampler assumption

The soundness theorem assumes a common finite coin alphabet whose decoders have
uniform fibers at every challenge role.  The product alphabet below exhibits
such decoders simultaneously for both initial tuples, both sides' field pairs,
field elements, Ligero challenges and query sets, and the MAC challenge.

This is an abstract sampling model.  It makes no claim about converting a
fixed-length digest or the deployed byte stream into these coins.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.IdealSampler

open Lfzk.TwoFieldV1Rows

variable (I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac : Type)
  [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
  [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁]
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂] [Fintype Fmac] [DecidableEq Fmac]

/-- One shared ideal coin for every role of a two-field ZK execution. -/
abbrev Coins := I₁ × (I₂ × TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac)

/-- Extend an exact decoder on the existing two-field coins across the two
initial-tuple coordinates. -/
def lift {Y : Type} [Fintype Y] [DecidableEq Y]
    (d : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Y) :
    ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Y :=
  (d.snd I₂).snd I₁

def initial₁ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) I₁ :=
  (ExactDecoder.self I₁).fst _

def initial₂ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) I₂ :=
  ((ExactDecoder.self I₂).fst _).snd I₁

def pair₁ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₁ × F₁) :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1

def element₁ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₁ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1

def challenge₁ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₁ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1

def query₁ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₁ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2

def pair₂ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₂ × F₂) :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1

def element₂ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₂ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1

def challenge₂ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₂ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1

def query₂ : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₂ :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2

def mac : ExactDecoder (Coins I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Fmac :=
  lift I₁ I₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac)

end Lfzk.IdealSampler
