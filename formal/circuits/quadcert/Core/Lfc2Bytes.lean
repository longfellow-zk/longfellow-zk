import quadcert.Core.Lfc2

/-!
# Unpacking a committed page into bytes

## The problem this solves

`Lfc2.Cursor` holds the current 4,096-byte page as one `Nat` — a 32,768-bit integer — and
`readByte` advances with `page := page / 256`, returning `page % 256`. The division results chain
through the cursor and are shared, but the **modulo results are forced only later**, when the
decoded values are compared against the emitted literals. At that point the kernel has to
materialise one multi-kilobyte bignum per byte and take a modulo of each.

Measured on SHA-256's layer 5 (`readDeltasChunk 148 1024 cur_5_d1`, serial, idle machine):

| what is forced | time | peak RSS |
|---|---:|---:|
| list spine and cursor chain only | 4.5 s | 0.78 GB |
| the decoded delta values | 175 s | 9.5 GB |
| full equality against the emitted literal | 173 s | **18.0 GB — kernel abort** |

That is the whole SHA decoder blocker. It is invisible on ECDSA2 only because its layers are an
order of magnitude smaller.

**The fix is validated.** `readDeltasChunkB` below, on the same 1,024 deltas of the same layer,
reading from the same bytes:

| reader | time | peak RSS |
|---|---:|---:|
| packed `Cursor` (`readDeltasChunk`), forcing values | 175 s | 9.5 GB |
| byte `BCursor` (`readDeltasChunkB`), forcing values | **4.5 s** | **0.83 GB** |

39x faster and 11x smaller, against a chunk that currently aborts the kernel at 18 GB.

## The fix

The packing exists so that a page is **one Lean literal** whose SHA-256 leaf hash is checkable by
kernel reduction. The *reader* has no use for it packed — it wants bytes. So supply the byte list
as advice and tie it to the committed page with `packBytes`, exactly the advice-plus-linear-check
shape `CompressedLayer.deltasOk` already uses for the delta tree. `readByte` then pops a `cons`:
O(1), no bignum, nothing retained.

The Merkle leaf hash keeps using the packed `Nat`, so **the root does not change**.

## Why the check is composed rather than run in one piece

`packBytes` folds `b + 256 * acc`, so each step multiplies a growing bignum — checking a whole
4,096-byte page in one `rfl` costs the same quadratic the fix is meant to remove.
`packBytes_append` splits it, so a generated certificate checks 64-byte pieces and composes them
in a balanced tree: `O(n log n)` with small constants, the same treatment
`readDeltasChunk_compose` gives the delta table.
-/

namespace Quadcert.Lfc2

/-- Little-endian packing of a byte list into one natural, matching `PackedBytes`. -/
def packBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * packBytes bs

@[simp] theorem packBytes_nil : packBytes [] = 0 := rfl

theorem packBytes_cons (b : Nat) (bs : List Nat) :
    packBytes (b :: bs) = b + 256 * packBytes bs := rfl

/-- **The composition lemma.** A page's check splits into independently checkable pieces, so no
    single `rfl` multiplies a 32,768-bit accumulator. -/
theorem packBytes_append (l r : List Nat) :
    packBytes (l ++ r) = packBytes l + 256 ^ l.length * packBytes r := by
  induction l with
  | nil => simp [packBytes]
  | cons b bs ih =>
      -- `Lfc2` does not import Mathlib, so this is core `Nat` lemmas only.
      simp only [List.cons_append, packBytes, ih, List.length_cons, Nat.pow_succ,
        Nat.mul_add, Nat.add_assoc]
      rw [Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]

/-- Every byte is in range. Checked once per page, linearly, alongside the packing. -/
def bytesOk : List Nat → Bool
  | [] => true
  | b :: bs => decide (b < 256) && bytesOk bs

theorem bytesOk_append : ∀ {l r : List Nat},
    bytesOk (l ++ r) = (bytesOk l && bytesOk r)
  | [], _ => by simp [bytesOk]
  | b :: bs, r => by
      simp only [List.cons_append, bytesOk, bytesOk_append (l := bs) (r := r), Bool.and_assoc]

/-! ### The byte cursor

`BCursor` mirrors `Cursor` field for field — same `pageRemaining`, same `remaining`, same page
list — so that `readByteB` can mirror `readByte` branch for branch and the refinement is a
structural induction rather than an arithmetic reconciliation. The only difference is that the
current page is a `List Nat` and the two operations `page % 256` / `page / 256` become `head` and
`tail`. -/

structure BCursor where
  bytes : List Nat
  pageRemaining : Nat
  laterPages : List (List Nat)
  remaining : Nat
  deriving Repr, DecidableEq

/-- Consume one byte. Branch-for-branch the same as `Lfc2.readByte`; no arithmetic on the page. -/
def readByteB (cursor : BCursor) : Except Error (Nat × BCursor) :=
  if cursor.remaining = 0 then
    .error .unexpectedEnd
  else if cursor.pageRemaining = 0 then
    .error .badPageCount
  else
    match cursor.bytes with
    | [] => .error .badPageCount
    | b :: bs =>
      let remaining := cursor.remaining - 1
      if cursor.pageRemaining = 1 then
        if remaining = 0 then
          .ok (b, { bytes := [], pageRemaining := 0,
                    laterPages := cursor.laterPages, remaining := 0 })
        else
          match cursor.laterPages with
          | [] => .error .badPageCount
          | next :: rest =>
              .ok (b, { bytes := next, pageRemaining := min pageSize remaining,
                        laterPages := rest, remaining := remaining })
      else
        .ok (b, { cursor with bytes := bs, pageRemaining := cursor.pageRemaining - 1,
                              remaining := remaining })

/-! ### The refinement

`Refines c bc` says the byte cursor is a faithful unpacking of the packed one. It is what makes
the byte list *checked advice* rather than something trusted: `packBytes bs = page` is a linear
per-page identity, composed by `packBytes_append`, and everything else is a length or a bound. -/

/-- Later pages agree pagewise. A page must be at least `pageSize` long, because `readByte`
    sets `pageRemaining := min pageSize remaining` when it opens one. -/
def PagesRefine : List Nat → List (List Nat) → Prop
  | [], [] => True
  | p :: ps, bs :: bss =>
      packBytes bs = p ∧ bytesOk bs = true ∧ pageSize ≤ bs.length ∧ PagesRefine ps bss
  | _, _ => False

structure Refines (c : Cursor) (bc : BCursor) : Prop where
  rem : c.remaining = bc.remaining
  pageRem : c.pageRemaining = bc.pageRemaining
  packed : packBytes bc.bytes = c.page
  ok : bytesOk bc.bytes = true
  long : c.pageRemaining ≤ bc.bytes.length
  later : PagesRefine c.laterPages bc.laterPages

/-! The two arithmetic facts the whole refinement rests on: with every byte in range, packing is
invertible one byte at a time. -/

theorem packBytes_mod (b : Nat) (bs : List Nat) (hb : b < 256) :
    packBytes (b :: bs) % 256 = b := by
  rw [packBytes_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem packBytes_div (b : Nat) (bs : List Nat) (hb : b < 256) :
    packBytes (b :: bs) / 256 = packBytes bs := by
  rw [packBytes_cons, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem bytesOk_head {b : Nat} {bs : List Nat} (h : bytesOk (b :: bs) = true) : b < 256 := by
  simp only [bytesOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem bytesOk_tail {b : Nat} {bs : List Nat} (h : bytesOk (b :: bs) = true) :
    bytesOk bs = true := by
  simp only [bytesOk, Bool.and_eq_true] at h
  exact h.2

/-- **The step.** Whatever the byte reader returns, the packed reader returns the same byte and a
    cursor the new byte cursor still refines. This is the only place the packed representation is
    touched at all. -/
theorem readByte_refines {c : Cursor} {bc : BCursor} (h : Refines c bc)
    {b : Nat} {bc' : BCursor} (hb : readByteB bc = .ok (b, bc')) :
    ∃ c', readByte c = .ok (b, c') ∧ Refines c' bc' := by
  obtain ⟨hrem, hpr, hpack, hok, hlong, hlater⟩ := h
  -- both readers reject on the same two guards
  simp only [readByteB] at hb
  by_cases hr : bc.remaining = 0
  · simp only [hr, if_true] at hb; contradiction
  by_cases hp : bc.pageRemaining = 0
  · simp only [hr, hp, if_false, if_true] at hb; contradiction
  simp only [hr, hp, if_false] at hb
  cases hbytes : bc.bytes with
  | nil => rw [hbytes] at hb; simp only at hb; contradiction
  | cons x xs =>
    rw [hbytes] at hb hpack hok
    have hx : x < 256 := bytesOk_head hok
    have hbyte : c.page % 256 = x := by rw [← hpack]; exact packBytes_mod x xs hx
    have hdiv : c.page / 256 = packBytes xs := by rw [← hpack]; exact packBytes_div x xs hx
    have hr' : c.remaining ≠ 0 := by rw [hrem]; exact hr
    have hp' : c.pageRemaining ≠ 0 := by rw [hpr]; exact hp
    simp only [readByte, hr', hp', if_false, hbyte]
    by_cases h1 : bc.pageRemaining = 1
    · have h1' : c.pageRemaining = 1 := by rw [hpr]; exact h1
      simp only [h1] at hb
      simp only [h1', if_true]
      by_cases hz : bc.remaining - 1 = 0
      · have hz' : c.remaining - 1 = 0 := by rw [hrem]; exact hz
        simp only [hz] at hb
        simp only [hz', if_true]
        cases hb
        refine ⟨_, rfl, ⟨by simp [hrem, hz'], rfl, by simp [packBytes], by simp [bytesOk],
          by simp, hlater⟩⟩
      · have hz' : c.remaining - 1 ≠ 0 := by rw [hrem]; exact hz
        simp only [hz] at hb
        simp only [hz', if_false]
        cases hlp : bc.laterPages with
        | nil =>
            rw [hlp] at hb; simp only at hb; contradiction
        | cons nb rest =>
            rw [hlp] at hb hlater
            cases hcp : c.laterPages with
            | nil => rw [hcp] at hlater; simp only [PagesRefine] at hlater
            | cons np crest =>
                rw [hcp] at hlater
                obtain ⟨hnp, hnok, hnlen, hrest⟩ := hlater
                simp only at hb
                cases hb
                refine ⟨_, rfl, ⟨by simp [hrem], by simp [hrem], hnp, hnok, ?_, hrest⟩⟩
                exact Nat.le_trans (Nat.min_le_left _ _) hnlen
    · have h1' : c.pageRemaining ≠ 1 := by rw [hpr]; exact h1
      simp only [h1] at hb
      simp only [h1', if_false]
      -- hoisted: `cases hb` substitutes the cursor and `x`, `xs` go out of scope
      have hlen' : bc.pageRemaining ≤ xs.length + 1 := by
        have h2 : c.pageRemaining ≤ (x :: xs).length := by rw [← hbytes]; exact hlong
        rw [hpr] at h2
        simpa only [List.length_cons] using h2
      cases hb
      refine ⟨_, rfl, ⟨by simp [hrem], by simp [hpr], hdiv.symm, bytesOk_tail hok, ?_, hlater⟩⟩
      simp only [hpr]
      omega

/-- ULEB128, over the byte cursor. Mirrors `Lfc2.readUlebLoop` clause for clause, including the
    non-canonical rejection, so the refinement is an induction on fuel and nothing else. -/
def readUlebLoopB : Nat → Nat → Nat → BCursor → Except Error (Nat × BCursor)
  | 0, _, _, _ => .error .ulebOverflow
  | fuel + 1, index, value, cursor => do
      let (byte, cursor) ← readByteB cursor
      let payload := byte % 128
      let value := value + payload * 128 ^ index
      if byte < 128 then
        if index > 0 && payload = 0 then .error .noncanonicalUleb else .ok (value, cursor)
      else
        readUlebLoopB fuel (index + 1) value cursor

def readUlebB (cursor : BCursor) : Except Error (Nat × BCursor) :=
  readUlebLoopB 4 0 0 cursor

theorem readUlebLoop_refines : ∀ (fuel index value : Nat) {c : Cursor} {bc : BCursor},
    Refines c bc → ∀ {v : Nat} {bc' : BCursor},
    readUlebLoopB fuel index value bc = .ok (v, bc') →
    ∃ c', readUlebLoop fuel index value c = .ok (v, c') ∧ Refines c' bc'
  | 0, _, _, _, _, _, _, _, hb => by simp only [readUlebLoopB] at hb; contradiction
  | fuel + 1, index, value, c, bc, h, v, bc', hb => by
      simp only [readUlebLoopB, bind, Except.bind] at hb
      cases hread : readByteB bc with
      | error e => rw [hread] at hb; contradiction
      | ok pair =>
          rcases pair with ⟨byte, bmid⟩
          rw [hread] at hb
          obtain ⟨cmid, hcread, hmid⟩ := readByte_refines h hread
          simp only [readUlebLoop, bind, Except.bind, hcread]
          simp only at hb ⊢
          by_cases hlt : byte < 128
          · simp only [hlt, if_true] at hb ⊢
            by_cases hnc : index > 0 && byte % 128 = 0
            · simp only [hnc, if_true] at hb; contradiction
            · simp only [hnc, if_false] at hb ⊢
              cases hb
              exact ⟨cmid, rfl, hmid⟩
          · simp only [hlt, if_false] at hb ⊢
            exact readUlebLoop_refines fuel (index + 1) _ hmid hb

theorem readUleb_refines {c : Cursor} {bc : BCursor} (h : Refines c bc)
    {v : Nat} {bc' : BCursor} (hb : readUlebB bc = .ok (v, bc')) :
    ∃ c', readUleb c = .ok (v, c') ∧ Refines c' bc' :=
  readUlebLoop_refines 4 0 0 h hb

/-- `readDeltasChunk`, over the byte cursor. Same grammar, same bounds check; the only
    difference is where the bytes come from. Kept here so the win can be measured against the
    packed reader on identical input before `Lfc2` is changed. -/
def readDeltasChunkB (constantCount : Nat) :
    Nat → BCursor → Except Error (List Delta × BCursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let (g, cursor) ← readUlebB cursor
      let (h0, cursor) ← readUlebB cursor
      let (h1, cursor) ← readUlebB cursor
      let (kIndex, cursor) ← readUlebB cursor
      if !(kIndex < constantCount) then .error .constantIndexOutOfBounds else
      let (deltas, cursor) ← readDeltasChunkB constantCount count cursor
      .ok ({ g := decodeDelta g, h0 := decodeDelta h0,
             h1 := decodeDelta h1, kIndex := kIndex } :: deltas, cursor)

/-- **The lift.** Whatever the byte reader produces for a chunk, the packed reader produces the
    same deltas and a cursor the new byte cursor still refines. This is what lets a generated
    certificate prove the fast version by `rfl` and transfer the result to the statement `decode`
    actually needs — 4.5 s instead of 175 s, with `Cursor` and every existing module untouched. -/
theorem readDeltasChunk_refines (constantCount : Nat) :
    ∀ (n : Nat) {c : Cursor} {bc : BCursor}, Refines c bc →
    ∀ {l : List Delta} {bc' : BCursor},
    readDeltasChunkB constantCount n bc = .ok (l, bc') →
    ∃ c', readDeltasChunk constantCount n c = .ok (l, c') ∧ Refines c' bc'
  | 0, c, bc, h, l, bc', hb => by
      simp only [readDeltasChunkB] at hb
      cases hb
      exact ⟨c, rfl, h⟩
  | n + 1, c, bc, h, l, bc', hb => by
      simp only [readDeltasChunkB, bind, Except.bind] at hb
      cases hg : readUlebB bc with
      | error e => rw [hg] at hb; contradiction
      | ok pg =>
        rcases pg with ⟨g, b1⟩
        rw [hg] at hb; simp only at hb
        obtain ⟨c1, hcg, h1⟩ := readUleb_refines h hg
        cases h0 : readUlebB b1 with
        | error e => rw [h0] at hb; contradiction
        | ok p0 =>
          rcases p0 with ⟨v0, b2⟩
          rw [h0] at hb; simp only at hb
          obtain ⟨c2, hc0, h2⟩ := readUleb_refines h1 h0
          cases h1' : readUlebB b2 with
          | error e => rw [h1'] at hb; contradiction
          | ok p1 =>
            rcases p1 with ⟨v1, b3⟩
            rw [h1'] at hb; simp only at hb
            obtain ⟨c3, hc1, h3⟩ := readUleb_refines h2 h1'
            cases hk : readUlebB b3 with
            | error e => rw [hk] at hb; contradiction
            | ok pk =>
              rcases pk with ⟨k, b4⟩
              rw [hk] at hb; simp only at hb
              obtain ⟨c4, hck, h4⟩ := readUleb_refines h3 hk
              simp only [readDeltasChunk, bind, Except.bind, hcg, hc0, hc1, hck]
              by_cases hbnd : k < constantCount
              · simp only [hbnd, decide_true, Bool.not_true, if_false,
                  Bool.false_eq_true] at hb ⊢
                cases hrest : readDeltasChunkB constantCount n b4 with
                | error e => rw [hrest] at hb; contradiction
                | ok pr =>
                  rcases pr with ⟨ds, b5⟩
                  rw [hrest] at hb; simp only at hb
                  obtain ⟨c5, hcr, h5⟩ := readDeltasChunk_refines constantCount n h4 hrest
                  rw [hcr]; simp only
                  cases hb
                  exact ⟨c5, rfl, h5⟩
              · simp only [hbnd, decide_false, Bool.not_false, if_true] at hb
                contradiction

/-! ### Uniqueness

`readDeltasChunk_refines` produces *some* packed cursor. A generated certificate has to land on
the specific `cur_l_dk` the next chunk starts from, so the refinement has to determine it — and it
does: every field of `Cursor` is a function of the byte cursor. `PagesRefine`'s catch-all arm
makes the two page lists the same length, which is what pins `laterPages`. -/

theorem PagesRefine_unique : ∀ {ps qs : List Nat} {bss : List (List Nat)},
    PagesRefine ps bss → PagesRefine qs bss → ps = qs
  | [], [], [], _, _ => rfl
  | [], _ :: _, [], _, h => by simp only [PagesRefine] at h
  | _ :: _, [], [], h, _ => by simp only [PagesRefine] at h
  | [], _, _ :: _, h, _ => by simp only [PagesRefine] at h
  | _ :: _, [], _ :: _, _, h => by simp only [PagesRefine] at h
  | p :: ps, q :: qs, bs :: bss, h1, h2 => by
      obtain ⟨hp, _, _, hr1⟩ := h1
      obtain ⟨hq, _, _, hr2⟩ := h2
      rw [← hp, ← hq, PagesRefine_unique hr1 hr2]

theorem Refines_unique {c₁ c₂ : Cursor} {bc : BCursor}
    (h₁ : Refines c₁ bc) (h₂ : Refines c₂ bc) : c₁ = c₂ := by
  obtain ⟨r1, p1, k1, _, _, l1⟩ := h₁
  obtain ⟨r2, p2, k2, _, _, l2⟩ := h₂
  cases c₁; cases c₂
  simp only [Cursor.mk.injEq]
  exact ⟨by simp_all, by simp_all, PagesRefine_unique l1 l2, by simp_all⟩

/-- **What a generated certificate uses.** Prove the chunk with the byte reader, name the packed
    cursor the next chunk starts from, and this transfers the result to the statement `decode`
    consumes. -/
theorem readDeltasChunk_transfer (constantCount n : Nat)
    {cstart cstop : Cursor} {bstart bstop : BCursor} {l : List Delta}
    (hstart : Refines cstart bstart) (hstop : Refines cstop bstop)
    (fast : readDeltasChunkB constantCount n bstart = .ok (l, bstop)) :
    readDeltasChunk constantCount n cstart = .ok (l, cstop) := by
  obtain ⟨c', hslow, href⟩ := readDeltasChunk_refines constantCount n hstart fast
  rwa [Refines_unique href hstop] at hslow

/-! ### Building the refinement at a cursor offset

`cursorAt` is where a generated certificate enters the reader, so this is the last thing needed
before the fast path can be used: given the byte pages, produce a `BCursor` at the same offset
and a `Refines` between them. -/

/-- Dropping `n` bytes divides the packing by `256 ^ n` — the byte-list counterpart of the
    `>>> (8 * within)` in `cursorAt`. -/
theorem packBytes_drop : ∀ (n : Nat) (l : List Nat), bytesOk l = true →
    packBytes (l.drop n) = packBytes l / 256 ^ n
  | 0, l, _ => by simp
  | _ + 1, [], _ => by simp [packBytes]
  | n + 1, b :: bs, h => by
      have hb : b < 256 := bytesOk_head h
      rw [List.drop_succ_cons, packBytes_drop n bs (bytesOk_tail h), Nat.pow_succ,
        Nat.mul_comm (256 ^ n) 256, ← Nat.div_div_eq_div_mul, packBytes_div b bs hb]

theorem bytesOk_drop : ∀ (n : Nat) (l : List Nat), bytesOk l = true → bytesOk (l.drop n) = true
  | 0, l, h => by simpa using h
  | _ + 1, [], _ => by simp [bytesOk]
  | n + 1, _ :: bs, h => by
      rw [List.drop_succ_cons]; exact bytesOk_drop n bs (bytesOk_tail h)

theorem length_drop_ge : ∀ (n : Nat) (l : List Nat), l.length - n ≤ (l.drop n).length := by
  intro n l; simp

/-- `cursorAt`, over byte pages. Mirrors the packed version: same page index, same
    `pageRemaining`, same `remaining`; `>>> (8 * within)` becomes `drop within`. -/
def bcursorAt (byteLength : Nat) (pages : List (List Nat)) (offset : Nat) : BCursor :=
  let page := offset / pageSize
  let within := offset % pageSize
  { bytes := (pages.getD page []).drop within
    pageRemaining := min pageSize (byteLength - page * pageSize) - within
    laterPages := pages.drop (page + 1)
    remaining := byteLength - offset }

/-- Pagewise agreement between the packed page list and the byte page list, from position `k`
    on. Stated as a fuel-driven recursion so it composes with `List.drop`. -/
theorem PagesRefine_drop : ∀ (k : Nat) (ps : List Nat) (bss : List (List Nat)),
    PagesRefine ps bss → PagesRefine (ps.drop k) (bss.drop k)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], h => by simp [PagesRefine]
  | k + 1, p :: ps, bs :: bss, h => by
      obtain ⟨_, _, _, hrest⟩ := h
      simpa using PagesRefine_drop k ps bss hrest
  | _ + 1, [], _ :: _, h => by simp only [PagesRefine] at h
  | _ + 1, _ :: _, [], h => by simp only [PagesRefine] at h

theorem PagesRefine_getD : ∀ (k : Nat) (ps : List Nat) (bss : List (List Nat)),
    PagesRefine ps bss → k < ps.length →
    packBytes (bss.getD k []) = ps.getD k 0 ∧ bytesOk (bss.getD k []) = true ∧
      pageSize ≤ (bss.getD k []).length
  | _, [], _, _, hk => by simp at hk
  | 0, p :: _, [], h, _ => by simp only [PagesRefine] at h
  | 0, p :: ps, bs :: bss, h, _ => by
      obtain ⟨hp, hok, hlen, _⟩ := h
      exact ⟨by simpa using hp, by simpa using hok, by simpa using hlen⟩
  | k + 1, _ :: _, [], h, _ => by simp only [PagesRefine] at h
  | k + 1, p :: ps, bs :: bss, h, hk => by
      obtain ⟨_, _, _, hrest⟩ := h
      have hk' : k < ps.length := by simpa using hk
      simpa using PagesRefine_getD k ps bss hrest hk'

private theorem shiftRight_eq_div_pow256 (x n : Nat) : x >>> (8 * n) = x / 256 ^ n := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- **Entering the reader.** At any offset, the byte cursor built from the checked page lists
    refines the packed cursor the generated modules already name. This is what a certificate
    supplies to `readDeltasChunk_refines`. -/
theorem cursorAt_refines (input : PackedBytes) (pages : List (List Nat)) (offset : Nat)
    (hpages : PagesRefine input.pages pages)
    (hpage : offset / pageSize < input.pages.length) :
    Refines (cursorAt input offset) (bcursorAt input.byteLength pages offset) := by
  obtain ⟨hp, hok, hlen⟩ := PagesRefine_getD (offset / pageSize) _ _ hpages hpage
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- the page value: `drop` on bytes is `>>> (8 * within)` on the packing
    show packBytes ((pages.getD (offset / pageSize) []).drop (offset % pageSize)) = _
    rw [packBytes_drop _ _ hok, hp]
    exact (shiftRight_eq_div_pow256 _ _).symm
  · exact bytesOk_drop _ _ hok
  · show _ ≤ ((pages.getD (offset / pageSize) []).drop (offset % pageSize)).length
    rw [List.length_drop]
    exact Nat.sub_le_sub_right (Nat.le_trans (Nat.min_le_left _ _) hlen) _
  · exact PagesRefine_drop _ _ _ hpages

/-! ### The segment dictionary

Same treatment. `readSegmentsChunk` reads a length then that many indices, so it needs two more
mirrors: `readBoundedB` and `readIndexListChunkB`. Nothing new happens in the proofs — each is
the same `cases` chain over the reader's clauses with `readByte_refines` at the bottom. -/

def readBoundedB (maximum : Nat) (cursor : BCursor) : Except Error (Nat × BCursor) := do
  let (value, cursor) ← readUlebB cursor
  if value ≤ maximum then .ok (value, cursor) else .error .excessiveCount

theorem readBounded_refines {maximum : Nat} {c : Cursor} {bc : BCursor} (h : Refines c bc)
    {v : Nat} {bc' : BCursor} (hb : readBoundedB maximum bc = .ok (v, bc')) :
    ∃ c', readBounded maximum c = .ok (v, c') ∧ Refines c' bc' := by
  simp only [readBoundedB, bind, Except.bind] at hb
  cases hu : readUlebB bc with
  | error e => rw [hu] at hb; contradiction
  | ok pu =>
      rcases pu with ⟨value, bmid⟩
      rw [hu] at hb; simp only at hb
      obtain ⟨cmid, hcu, hmid⟩ := readUleb_refines h hu
      simp only [readBounded, bind, Except.bind, hcu]
      by_cases hle : value ≤ maximum
      · simp only [hle, if_true] at hb ⊢
        cases hb
        exact ⟨cmid, rfl, hmid⟩
      · simp only [hle, if_false] at hb; contradiction

def readIndexListChunkB (bound : Nat) (outOfBounds : Error) :
    Nat → BCursor → Except Error (List Nat × BCursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let (value, cursor) ← readUlebB cursor
      if !(value < bound) then .error outOfBounds else
      let (values, cursor) ← readIndexListChunkB bound outOfBounds count cursor
      .ok (value :: values, cursor)

theorem readIndexListChunk_refines (bound : Nat) (oob : Error) :
    ∀ (n : Nat) {c : Cursor} {bc : BCursor}, Refines c bc →
    ∀ {l : List Nat} {bc' : BCursor},
    readIndexListChunkB bound oob n bc = .ok (l, bc') →
    ∃ c', readIndexListChunk bound oob n c = .ok (l, c') ∧ Refines c' bc'
  | 0, c, bc, h, l, bc', hb => by
      simp only [readIndexListChunkB] at hb; cases hb; exact ⟨c, rfl, h⟩
  | n + 1, c, bc, h, l, bc', hb => by
      simp only [readIndexListChunkB, bind, Except.bind] at hb
      cases hu : readUlebB bc with
      | error e => rw [hu] at hb; contradiction
      | ok pu =>
          rcases pu with ⟨value, b1⟩
          rw [hu] at hb; simp only at hb
          obtain ⟨c1, hcu, h1⟩ := readUleb_refines h hu
          simp only [readIndexListChunk, bind, Except.bind, hcu]
          by_cases hlt : value < bound
          · simp only [hlt, decide_true, Bool.not_true, if_false, Bool.false_eq_true] at hb ⊢
            cases hr : readIndexListChunkB bound oob n b1 with
            | error e => rw [hr] at hb; contradiction
            | ok pr =>
                rcases pr with ⟨vs, b2⟩
                rw [hr] at hb; simp only at hb
                obtain ⟨c2, hcr, h2⟩ := readIndexListChunk_refines bound oob n h1 hr
                rw [hcr]; simp only
                cases hb
                exact ⟨c2, rfl, h2⟩
          · simp only [hlt, decide_false, Bool.not_false, if_true] at hb; contradiction

def readSegmentsChunkB (deltaCount : Nat) :
    Nat → Nat → BCursor → Except Error (List (Array Nat) × Nat × BCursor)
  | 0, symbols, cursor => .ok ([], symbols, cursor)
  | count + 1, symbols, cursor => do
      let (length, cursor) ← readBoundedB maxTermsPerLayer cursor
      let symbols := symbols + length
      if symbols > maxTermsPerLayer then .error .excessiveCount else
      let (segment, cursor) ←
        readIndexListChunkB deltaCount .deltaIndexOutOfBounds length cursor
      let (segments, symbols, cursor) := ← readSegmentsChunkB deltaCount count symbols cursor
      .ok (Array.mk segment :: segments, symbols, cursor)

theorem readSegmentsChunk_refines (deltaCount : Nat) :
    ∀ (n s : Nat) {c : Cursor} {bc : BCursor}, Refines c bc →
    ∀ {l : List (Array Nat)} {s' : Nat} {bc' : BCursor},
    readSegmentsChunkB deltaCount n s bc = .ok (l, s', bc') →
    ∃ c', readSegmentsChunk deltaCount n s c = .ok (l, s', c') ∧ Refines c' bc'
  | 0, s, c, bc, h, l, s', bc', hb => by
      simp only [readSegmentsChunkB] at hb; cases hb; exact ⟨c, rfl, h⟩
  | n + 1, s, c, bc, h, l, s', bc', hb => by
      simp only [readSegmentsChunkB, bind, Except.bind] at hb
      cases hlen : readBoundedB maxTermsPerLayer bc with
      | error e => rw [hlen] at hb; contradiction
      | ok pl =>
          rcases pl with ⟨length, b1⟩
          rw [hlen] at hb; simp only at hb
          obtain ⟨c1, hcl, h1⟩ := readBounded_refines h hlen
          simp only [readSegmentsChunk, bind, Except.bind, hcl]
          by_cases hbud : s + length > maxTermsPerLayer
          · simp only [hbud, if_true] at hb; contradiction
          · simp only [hbud, if_false] at hb ⊢
            cases hseg : readIndexListChunkB deltaCount .deltaIndexOutOfBounds length b1 with
            | error e => rw [hseg] at hb; contradiction
            | ok ps =>
                rcases ps with ⟨segment, b2⟩
                rw [hseg] at hb; simp only at hb
                obtain ⟨c2, hcs, h2⟩ :=
                  readIndexListChunk_refines deltaCount .deltaIndexOutOfBounds length h1 hseg
                rw [hcs]; simp only
                cases hrest : readSegmentsChunkB deltaCount n (s + length) b2 with
                | error e => rw [hrest] at hb; contradiction
                | ok pr =>
                    rcases pr with ⟨segs, s2, b3⟩
                    rw [hrest] at hb; simp only at hb
                    obtain ⟨c3, hcr, h3⟩ :=
                      readSegmentsChunk_refines deltaCount n (s + length) h2 hrest
                    rw [hcr]; simp only
                    cases hb
                    exact ⟨c3, rfl, h3⟩

theorem readSegmentsChunk_transfer (deltaCount n s : Nat)
    {cstart cstop : Cursor} {bstart bstop : BCursor} {l : List (Array Nat)} {s' : Nat}
    (hstart : Refines cstart bstart) (hstop : Refines cstop bstop)
    (fast : readSegmentsChunkB deltaCount n s bstart = .ok (l, s', bstop)) :
    readSegmentsChunk deltaCount n s cstart = .ok (l, s', cstop) := by
  obtain ⟨c', hslow, href⟩ := readSegmentsChunk_refines deltaCount n s hstart fast
  rwa [Refines_unique href hstop] at hslow

/-! ### The token stream

The fourth and last packed-cursor site. `readCompressedTokens` reads a layer's whole token
stream — 2,847 tokens on SHA-256's layer 5 — so it hits the same wall as the delta table, and it
is what `ShaCompressedLayer5` failed on after the deltas and segments were switched.

Two more cursor-consuming mirrors are needed (`readPhrasesChunk`, `readPhraseRootsChunk`); the
term and token *counts* are computed by functions that never touch the cursor, so both sides call
the same ones and nothing has to be mirrored there. -/

/-! ### Indexed counting

Switching the cursor is not enough for the token stage. Measured on SHA-256's layer 5, with the
byte reader *and* structural counting loops in place:

```
(readCompressedTokensB 1775 segLens_5 bcur_5_s2).isOk = true   -- no literal comparison at all
  -> 125 s, exceeds the 12 GB cap
```

`isOk` forces the counts and nothing else, so this is neither the byte reading nor the comparison
against emitted literals. `countPhraseTerms` walks every segment reference in the layer — 89,048
terms' worth — and each does `lengths[segmentIndex]?` on a 1,775-entry `Array`, which is a list
walk: about `1.6 x 10^8` steps inside one `rfl`.

The cure is the one `deltasOk` / `deltaAt` already apply to the delta table: a positional search
tree as **untrusted advice**, tied back by two linear checks, answering in `log n`. The trees are
threaded through a *separate* counting path used only by the byte reader, so
`readCompressedTokens`, `readCompressedLayer` and `readCompressedLayer_eq_of_stages` keep their
shapes and every existing certificate still means what it did. -/

/-- Advice is valid for an array when it is well-formed and lists the same elements. `leaf` means
    "no advice supplied", and then lookups fall back to indexing. -/
def treeOk {α : Type} [DecidableEq α] (tree : PTree α) (a : Array α) : Bool :=
  match tree with
  | .leaf => true
  | _ => tree.checkSize.isSome && decide (tree.toList = a.toList)

def treeAt {α : Type} [DecidableEq α] (tree : PTree α) (a : Array α) (i : Nat) : Option α :=
  match tree with
  | .leaf => a[i]?
  | _ => tree.lookup i

theorem treeAt_eq {α : Type} [DecidableEq α] (tree : PTree α) (a : Array α)
    (h : treeOk tree a = true) (i : Nat) : treeAt tree a i = a[i]? := by
  cases tree with
  | leaf => rfl
  | node ls l x r =>
      simp only [treeOk, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨n, hn⟩, hlist⟩ := h
      show PTree.lookup (.node ls l x r) i = _
      rw [PTree.lookup_eq_getElem _ hn i, hlist]
      simp

/-- `countSegmentTermsLoop` with the length lookup going through advice. -/
def countSegmentTermsLoopT (tree : PTree Nat) (lengths : Array Nat) :
    List Nat → Nat → Except Error Nat
  | [], total => .ok total
  | segmentIndex :: rest, total =>
      match treeAt tree lengths segmentIndex with
      | none => .error .segmentIndexOutOfBounds
      | some size =>
          let total := total + size
          if total > maxTermsPerLayer then .error .excessiveExpansion
          else countSegmentTermsLoopT tree lengths rest total

theorem countSegmentTermsLoopT_eq (tree : PTree Nat) (lengths : Array Nat)
    (h : treeOk tree lengths = true) :
    ∀ (l : List Nat) (total : Nat),
      countSegmentTermsLoopT tree lengths l total = countSegmentTermsLoop lengths l total
  | [], _ => rfl
  | i :: rest, total => by
      simp only [countSegmentTermsLoopT, countSegmentTermsLoop, treeAt_eq tree lengths h i]
      cases lengths[i]? with
      | none => rfl
      | some size =>
          simp only
          by_cases hb : total + size > maxTermsPerLayer
          · simp only [hb, if_true]
          · simp only [hb, if_false]
            exact countSegmentTermsLoopT_eq tree lengths h rest (total + size)

def countSegmentTermsT (tree : PTree Nat) (lengths : Array Nat) (tokens : Array Nat)
    (initial : Nat := 0) : Except Error Nat :=
  countSegmentTermsLoopT tree lengths tokens.toList initial

theorem countSegmentTermsT_eq (tree : PTree Nat) (lengths : Array Nat)
    (h : treeOk tree lengths = true) (tokens : Array Nat) (initial : Nat) :
    countSegmentTermsT tree lengths tokens initial = countSegmentTerms lengths tokens initial :=
  countSegmentTermsLoopT_eq tree lengths h tokens.toList initial


/-- `readCompressedTokens`, over the byte cursor. `countSegmentTerms` is shared verbatim: it
    consumes the decoded array, never the cursor, so there is nothing in it to mirror. -/
def readCompressedTokensB (segmentCount : Nat) (lengths : Array Nat) (cursor : BCursor) :
    Except Error (Array Nat × Nat × Nat × BCursor) := do
  let (count, cursor) ← readBoundedB maxTermsPerLayer cursor
  let (tokens, cursor) ←
    readIndexListChunkB segmentCount .segmentIndexOutOfBounds count cursor
  let tokens := Array.mk tokens
  let termCount ← countSegmentTerms lengths tokens
  .ok (tokens, tokens.size, termCount, cursor)

theorem readCompressedTokens_refines {segmentCount : Nat} {lengths : Array Nat}
    {c : Cursor} {bc : BCursor} (h : Refines c bc)
    {t : Array Nat} {tc tm : Nat} {bc' : BCursor}
    (hb : readCompressedTokensB segmentCount lengths bc = .ok (t, tc, tm, bc')) :
    ∃ c', readCompressedTokens segmentCount lengths c = .ok (t, tc, tm, c') ∧ Refines c' bc' := by
  simp only [readCompressedTokensB, bind, Except.bind] at hb
  simp only [readCompressedTokens, bind, Except.bind]
  cases hcnt : readBoundedB maxTermsPerLayer bc with
  | error e => rw [hcnt] at hb; contradiction
  | ok pc =>
      rcases pc with ⟨count, b2⟩
      rw [hcnt] at hb; simp only at hb
      obtain ⟨c2, hcc, h2⟩ := readBounded_refines h hcnt
      rw [hcc]; simp only
      cases htk : readIndexListChunkB segmentCount .segmentIndexOutOfBounds count b2 with
      | error e => rw [htk] at hb; contradiction
      | ok pt =>
          rcases pt with ⟨tokens, b3⟩
          rw [htk] at hb; simp only at hb
          obtain ⟨c3, hct, h3⟩ :=
            readIndexListChunk_refines segmentCount .segmentIndexOutOfBounds count h2 htk
          rw [hct]; simp only
          cases hterm : countSegmentTerms lengths (Array.mk tokens) with
          | error e => rw [hterm] at hb; contradiction
          | ok n =>
              rw [hterm] at hb
              simp only at hb ⊢
              cases hb
              exact ⟨c3, rfl, h3⟩
theorem readCompressedTokens_transfer (segmentCount : Nat) (lengths : Array Nat)
    {cstart cstop : Cursor} {bstart bstop : BCursor}
    {t : Array Nat} {tc tm : Nat}
    (hstart : Refines cstart bstart) (hstop : Refines cstop bstop)
    (fast : readCompressedTokensB segmentCount lengths bstart = .ok (t, tc, tm, bstop)) :
    readCompressedTokens segmentCount lengths cstart = .ok (t, tc, tm, cstop) := by
  obtain ⟨c', hslow, href⟩ := readCompressedTokens_refines hstart fast
  rwa [Refines_unique href hstop] at hslow

/-- The byte reader with the counting indexed. The tree is **checked inline** rather than taken
    as a hypothesis, in one linear pass. -/
def readCompressedTokensBT (segmentCount : Nat) (ltree : PTree Nat) (lengths : Array Nat)
    (cursor : BCursor) : Except Error (Array Nat × Nat × Nat × BCursor) := do
  if !treeOk ltree lengths then .error .badTokenEncoding else
  let (count, cursor) ← readBoundedB maxTermsPerLayer cursor
  let (tokens, cursor) ←
    readIndexListChunkB segmentCount .segmentIndexOutOfBounds count cursor
  let tokens := Array.mk tokens
  let termCount ← countSegmentTermsT ltree lengths tokens
  .ok (tokens, tokens.size, termCount, cursor)

theorem readCompressedTokensBT_eq {segmentCount : Nat} {ltree : PTree Nat} {lengths : Array Nat}
    {bc : BCursor} {r : Array Nat × Nat × Nat × BCursor}
    (h : readCompressedTokensBT segmentCount ltree lengths bc = .ok r) :
    readCompressedTokensB segmentCount lengths bc = .ok r := by
  simp only [readCompressedTokensBT, bind, Except.bind] at h
  by_cases hlt : treeOk ltree lengths = true
  · simp only [hlt, Bool.not_true, if_false, Bool.false_eq_true] at h
    simp only [readCompressedTokensB, bind, Except.bind]
    cases hcnt : readBoundedB maxTermsPerLayer bc with
    | error e => rw [hcnt] at h; contradiction
    | ok pc =>
        rcases pc with ⟨count, b2⟩
        rw [hcnt] at h; simp only at h ⊢
        cases htk : readIndexListChunkB segmentCount .segmentIndexOutOfBounds count b2 with
        | error e => rw [htk] at h; contradiction
        | ok pt =>
            rcases pt with ⟨tokens, b3⟩
            rw [htk] at h; simp only at h ⊢
            rwa [countSegmentTermsT_eq ltree lengths hlt (Array.mk tokens) 0] at h
  · simp only [Bool.not_eq_true] at hlt
    simp only [hlt, Bool.not_false, if_true] at h
    contradiction
/-- The whole chain in one step, for a generated certificate: prove the tree-indexed byte read by
    `rfl`, get the packed reader's statement. -/
theorem readCompressedTokens_transferT (segmentCount : Nat) (ltree : PTree Nat)
    (lengths : Array Nat)
    {cstart cstop : Cursor} {bstart bstop : BCursor}
    {t : Array Nat} {tc tm : Nat}
    (hstart : Refines cstart bstart) (hstop : Refines cstop bstop)
    (fast : readCompressedTokensBT segmentCount ltree lengths bstart
              = .ok (t, tc, tm, bstop)) :
    readCompressedTokens segmentCount lengths cstart = .ok (t, tc, tm, cstop) :=
  readCompressedTokens_transfer segmentCount lengths hstart hstop
    (readCompressedTokensBT_eq fast)

/-! `readDeltasChunk_compose` ports across unchanged in shape — the packed version in `Lfc2` is
a 40-line `induction`/`cases` chain over the four ULEB reads and the bounds check, and nothing in
it depends on how a byte is obtained. It is not repeated here because this module exists to
measure the byte extraction, not to be the final home of the reader. -/

end Quadcert.Lfc2
