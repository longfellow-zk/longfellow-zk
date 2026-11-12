import LfzkV2.Current.QueryRuntime
import LfzkV2.Current.ProofBodyBounds

/-! Canonical query prefixes are closed under actual transcript replay.
A producer supplies typed data for each public packet schema. The parsed
cache and physical block are constructed together; neither an arbitrary
cache equality nor a whole-replay canonicality certificate is an input. -/
noncomputable section
namespace LfzkV2.Current.CanonicalReplay
open CanonicalPrefix QueryRuntime
open scoped Classical

section Generic
variable {Key Fresh Body : Type} {capacity : ℕ}

/-- Typed data for every public packet. The values can be collected from a
particular replay, including data derived from earlier challenge answers. -/
def Values : List (Packet Fresh capacity) → Type
  | [] => Unit
  | packet :: tail => packet.Data × Values tail

namespace Values

def get : {packets : List (Packet Fresh capacity)} → Values packets →
    (i : Fin packets.length) → (packets.get i).Data
  | _ :: _, values, ⟨0,_⟩ => values.1
  | _ :: tail, values, ⟨n+1,hn⟩ => get values.2 ⟨n,by simpa using hn⟩

def ofFn : (packets : List (Packet Fresh capacity)) →
    ((i : Fin packets.length) → (packets.get i).Data) → Values packets
  | [], _ => ()
  | _ :: tail, data => (data ⟨0,by simp⟩,ofFn tail (fun i => data i.succ))

@[simp] theorem get_ofFn (packets : List (Packet Fresh capacity))
    (data : (i : Fin packets.length) → (packets.get i).Data) (i : Fin packets.length) :
    get (ofFn packets data) i = data i := by
  induction packets with
  | nil => exact Fin.elim0 i
  | cons packet tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun i => data i.succ) j

end Values

/-- The canonical prefix ending at a specified boundary, or at the final
seal. The terminal body retains exactly the checked u64 framing bound. -/
def valueAt (bodyCodec : PrefixCodec Body) :
    (packets : List (Packet Fresh capacity)) → Values packets →
      (Fin packets.length → Digest) → {body // (bodyCodec.encode body).length ≤ maxLength} →
        (n : ℕ) → n ≤ packets.length →
          QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)
  | [], _, _, body, _, _ => body
  | _ :: _, values, _, _, 0, _ => (values.1,.inl ())
  | packet :: tail, values, links, body, n+1, hn =>
      (values.1,.inr (links ⟨0,by simp⟩,
        valueAt bodyCodec tail values.2 (fun i => links i.succ) body n (by simpa using hn)))

/-- Advancing a logical query appends its current physical writes and the
actual answer link. It supplies no additional transcript boundary. -/
def next (body : Body) (block : Block capacity Fresh) (link : Digest) :
    {roles : List Role} → Input roles Key (Block capacity Fresh) Digest Body →
      Input roles Key (Block capacity Fresh) Digest Body
  | _, .finalSeal history previous => .finalSeal history previous
  | [], .round i _ _ => Fin.elim0 i
  | _ :: tail, .round i history current =>
      Fin.lastCases
        (fun (history : History Key (Block capacity Fresh) Digest tail.length) current =>
          Input.finalSeal (history,current,link) body)
        (fun (j : Fin tail.length) (history : History Key (Block capacity Fresh) Digest j.val) current =>
          Input.round j.succ (history,current,link) block)
        i history current

private theorem next_prepend (role : Role) (first : Block capacity Fresh) (firstLink : Digest)
    (body : Body) (block : Block capacity Fresh) (link : Digest) {roles : List Role}
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    next body block link (prepend role first firstLink point) =
      prepend role first firstLink (next body block link point) := by
  cases point with
  | round i history current =>
      cases roles with
      | nil => exact Fin.elim0 i
      | cons previous tail =>
          refine Fin.lastCases ?_ (fun j => ?_) i history current
          · intro history current
            change next body block link
              (Input.round (roles := role :: previous :: tail) (Fin.last (tail.length+1)) _ _) =
                prepend role first firstLink (next body block link (Input.round (roles := previous :: tail) (Fin.last tail.length) history current))
            simp only [next]
            erw [Fin.lastCases_last,Fin.lastCases_last]
            rfl
          · intro history current
            change next body block link
              (Input.round (roles := role :: previous :: tail) j.succ.castSucc _ _) =
                prepend role first firstLink (next body block link (Input.round (roles := previous :: tail) j.castSucc history current))
            simp only [next]
            erw [Fin.lastCases_castSucc,Fin.lastCases_castSucc]
            rfl
  | finalSeal history previous => rfl

/-- The embedding of two consecutive parsed prefixes has precisely the
same transition as the runtime replay state. -/
theorem embed_valueAt_succ (bodyCodec : PrefixCodec Body)
    (packets : List (Packet Fresh capacity)) (values : Values packets)
    (links : Fin packets.length → Digest)
    (body : {body // (bodyCodec.encode body).length ≤ maxLength})
    (n : ℕ) (hn : n < packets.length) (context : Key)
    (nextBlock : Block capacity Fresh)
    (hnext : ∀ h : n+1 < packets.length,
      nextBlock = (packets.get ⟨n+1,h⟩).block (Values.get values ⟨n+1,h⟩)) :
    embed bodyCodec context packets
        (valueAt bodyCodec packets values links body (n+1) (by omega)) =
      next body.val nextBlock (links ⟨n,hn⟩)
        (embed bodyCodec context packets (valueAt bodyCodec packets values links body n (by omega))) := by
  induction packets generalizing n with
  | nil => simp at hn
  | cons packet tail ih =>
      cases n with
      | zero =>
          cases tail with
          | nil =>
              rfl
          | cons second tail =>
              have hb := hnext (by simp)
              simp only [List.get_cons_succ,Values.get] at hb
              subst nextBlock
              change Input.round ⟨1,by simp⟩ (context,packet.block values.1,links ⟨0,hn⟩)
                (second.block values.2.1) = next body.val (second.block values.2.1) (links ⟨0,hn⟩)
                  (Input.round (roles := packet.role :: second.role :: tail.map Packet.role)
                    (Fin.castSucc ⟨0,by simp⟩) context (packet.block values.1))
              simp only [next]
              erw [Fin.lastCases_castSucc]
              rfl

      | succ n =>
          have hn' : n < tail.length := by simpa using hn
          have hi := ih values.2 (fun i => links i.succ) n hn'
            (by intro h; exact hnext (by simpa using h))
          simp only [valueAt,embed]
          rw [hi]
          exact (next_prepend _ _ _ _ _ _ _).symm


def terminalBody {roles : List Role} : Input roles Key (Block capacity Fresh) Digest Body → Option Body
  | .round .. => none
  | .finalSeal _ body => some body

private theorem history_ext {roles : List Role} (initial : Digest) (n : ℕ) (hn : n ≤ roles.length)
    (first second : History Key (Block capacity Fresh) Digest n)
    (hp : Input.previous (Body := Body) n hn first = Input.previous n hn second)
    (hl : Input.lastLink initial n first = Input.lastLink initial n second)
    (hc : Input.historyContext n first = Input.historyContext n second) : first = second := by
  cases n with
  | zero => exact hc
  | succ n =>
      rcases first with ⟨history,block,link⟩
      rcases second with ⟨history',block',link'⟩
      have he : (Input.round (roles := roles) (Body := Body) ⟨n,by omega⟩ history block) =
          Input.round ⟨n,by omega⟩ history' block' := Option.some.inj hp
      cases he
      change link = link' at hl
      cases hl
      rfl

/-- An input is recovered from its parent, feedback link and current data.
At rank zero its context supplies the initial prefix; at the final point
its body supplies the mandatory complete-proof message. -/
theorem point_ext {roles : List Role} (initial : Digest)
    (first second : Input roles Key (Block capacity Fresh) Digest Body)
    (hr : first.rank = second.rank) (hp : first.parent = second.parent)
    (hl : Input.claimed initial first = Input.claimed initial second)
    (hc : first.context = second.context) (hb : first.block = second.block)
    (ht : terminalBody first = terminalBody second) : first = second := by
  cases first with
  | round i history block =>
      cases second with
      | round j history' block' =>
          have hij : i = j := Fin.ext hr
          subst j
          have hblock : block = block' := Option.some.inj hb
          subst block'
          have hhistory := history_ext initial i.val (by omega) history history' hp hl hc
          cases hhistory
          rfl
      | finalSeal history' body =>
          have hi := i.isLt
          change i.val = roles.length at hr
          omega
  | finalSeal history body =>
      cases second with
      | round j history' block' =>
          have hj := j.isLt
          change roles.length = j.val at hr
          omega
      | finalSeal history' body' =>
          have hbody : body = body' := Option.some.inj ht
          subst body'
          have hhistory := history_ext initial roles.length (Nat.le_refl _) history history' hp hl hc
          cases hhistory
          rfl

private theorem next_parent (body : Body) (block : Block capacity Fresh) (link : Digest)
    {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (hr : point.rank < roles.length) : (next body block link point).parent = some point := by
  cases point with
  | finalSeal history previous => simp only [Input.rank] at hr; omega
  | round i history current =>
      cases roles with
      | nil => exact Fin.elim0 i
      | cons role tail =>
          refine Fin.lastCases ?_ (fun j => ?_) i history current
          · intro history current
            simp only [next]
            erw [Fin.lastCases_last]
            rfl
          · intro history current
            simp only [next]
            erw [Fin.lastCases_castSucc]
            rfl

private theorem next_claimed (body : Body) (block : Block capacity Fresh) (link initial : Digest)
    {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (hr : point.rank < roles.length) : Input.claimed initial (next body block link point) = link := by
  cases point with
  | finalSeal history previous => simp only [Input.rank] at hr; omega
  | round i history current =>
      cases roles with
      | nil => exact Fin.elim0 i
      | cons role tail =>
          refine Fin.lastCases ?_ (fun j => ?_) i history current
          · intro history current
            simp only [next]
            erw [Fin.lastCases_last]
            rfl
          · intro history current
            simp only [next]
            erw [Fin.lastCases_castSucc]
            rfl

private theorem prepend_rank {roles : List Role} (role : Role) (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).rank = point.rank+1 := by cases point <;> rfl

private theorem prepend_block {roles : List Role} (role : Role) (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).block = point.block := by cases point <;> rfl

private theorem prepend_terminalBody {roles : List Role} (role : Role) (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    terminalBody (prepend role block link point) = terminalBody point := by cases point <;> rfl

theorem embed_valueAt_rank (bodyCodec : PrefixCodec Body)
    (packets : List (Packet Fresh capacity)) (values : Values packets)
    (links : Fin packets.length → Digest)
    (body : {body // (bodyCodec.encode body).length ≤ maxLength})
    (n : ℕ) (hn : n ≤ packets.length) (context : Key) :
    (embed bodyCodec context packets (valueAt bodyCodec packets values links body n hn)).rank = n := by
  induction packets generalizing n with
  | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      rfl
  | cons packet tail ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [valueAt,embed]
          erw [prepend_rank]
          exact congrArg (·+1) (ih values.2 (fun i => links i.succ) n (by simpa using hn))

theorem embed_valueAt_block (bodyCodec : PrefixCodec Body)
    (packets : List (Packet Fresh capacity)) (values : Values packets)
    (links : Fin packets.length → Digest)
    (body : {body // (bodyCodec.encode body).length ≤ maxLength})
    (i : Fin packets.length) (context : Key) :
    (embed bodyCodec context packets (valueAt bodyCodec packets values links body i.val (by omega))).block =
      some ((packets.get i).block (Values.get values i)) := by
  induction packets with
  | nil => exact Fin.elim0 i
  | cons packet tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Fin.val_succ,valueAt,embed]
        erw [prepend_block]
        exact ih values.2 (fun i => links i.succ) j

theorem embed_valueAt_terminalBody (bodyCodec : PrefixCodec Body)
    (packets : List (Packet Fresh capacity)) (values : Values packets)
    (links : Fin packets.length → Digest)
    (body : {body // (bodyCodec.encode body).length ≤ maxLength})
    (n : ℕ) (hn : n ≤ packets.length) (context : Key) :
    terminalBody (embed bodyCodec context packets (valueAt bodyCodec packets values links body n hn)) =
      if n = packets.length then some body.val else none := by
  induction packets generalizing n with
  | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      rfl
  | cons packet tail ih =>
      cases n with
      | zero => simp only [valueAt,embed,terminalBody,List.length_cons,Nat.zero_ne_add_one,if_false]
      | succ n =>
          simp only [valueAt,embed]
          erw [prepend_terminalBody]
          simpa only [List.length_cons,Nat.add_right_cancel_iff] using
            ih values.2 (fun i => links i.succ) n (by simpa using hn)

@[simp] theorem reindex_rank {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) : (reindex h point).rank = point.rank := by cases h; rfl

@[simp] theorem reindex_block {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) : (reindex h point).block = point.block := by cases h; rfl

@[simp] theorem reindex_terminalBody {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) : terminalBody (reindex h point) = terminalBody point := by cases h; rfl

@[simp] theorem reindex_parent {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    (reindex h point).parent = point.parent.map (reindex h) := by
  cases h
  change point.parent = point.parent.map id
  rw [Option.map_id]
  rfl

@[simp] theorem reindex_claimed (initial : Digest) {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    Input.claimed initial (reindex h point) = Input.claimed initial point := by cases h; rfl

@[simp] theorem reindex_next (body : Body) (block : Block capacity Fresh) (link : Digest)
    {first second : List Role} (h : first = second) (point : Input first Key (Block capacity Fresh) Digest Body) :
    reindex h (next body block link point) = next body block link (reindex h point) := by cases h; rfl


private theorem parent_zero {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (hr : point.rank = 0) : point.parent = none := by
  cases point with
  | round i history block =>
      rcases i with ⟨n,hn⟩
      change n = 0 at hr
      subst n
      rfl
  | finalSeal history body =>
      change roles.length = 0 at hr
      cases roles with
      | nil => rfl
      | cons role tail => simp at hr

private theorem claimed_zero (initial : Digest) {roles : List Role}
    (point : Input roles Key (Block capacity Fresh) Digest Body) (hr : point.rank = 0) :
    Input.claimed initial point = initial := by
  cases point with
  | round i history block =>
      rcases i with ⟨n,hn⟩
      change n = 0 at hr
      subst n
      rfl
  | finalSeal history body =>
      change roles.length = 0 at hr
      cases roles with
      | nil => rfl
      | cons role tail => simp at hr

private theorem block_none {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (hr : point.rank = roles.length) : point.block = none := by
  cases point with
  | round i history block =>
      have hi := i.isLt
      change i.val = roles.length at hr
      omega
  | finalSeal history body => rfl

def pointAt (bodyCodec : PrefixCodec Body) (packets : List (Packet Fresh capacity))
    {roles : List Role} (hroles : packets.map Packet.role = roles) (context : Key)
    (values : Values packets) (links : Fin packets.length → Digest)
    (body : {body // (bodyCodec.encode body).length ≤ maxLength})
    (n : ℕ) (hn : n ≤ packets.length) : Input roles Key (Block capacity Fresh) Digest Body :=
  reindex hroles (embed bodyCodec context packets (valueAt bodyCodec packets values links body n hn))

end Generic

section Replay
variable {g : Geometry} {fields : Fields} {Advice Auth Key Fresh C : Type} {capacity : ℕ}
variable (e : Replay.Encoding g fields Advice Auth Key (Block capacity Fresh) C)
variable (bodyCodec : PrefixCodec (Body g fields Advice Auth))
variable (packets : List (Packet Fresh capacity)) (hroles : packets.map Packet.role = g.roles)
variable (producer : Replay.Output g fields Advice Auth → (i : Fin packets.length) →
  (Fin i.val → C) → (packets.get i).Data)

/-- The representation identity is discharged by the packet-based encoding
constructor. It concerns actual physical writes and parsed caches together. -/
private def index (i : Fin packets.length) : Fin g.roles.length :=
  Fin.cast (by simpa only [List.length_map] using congrArg List.length hroles) i

/-- Collect the actual packet data using the same strict-prefix challenge
tape as the runtime encoder. This is a witness for canonicality, not extra
serialized proof data. -/
def replayValues (initialLink : Digest) (proof : Replay.Output g fields Advice Auth)
    (H : Replay.Point g fields Advice Auth Key (Block capacity Fresh) → Digest × C) : Values packets :=
  Values.ofFn packets (fun i => producer proof i
    (fun j => (H ((e.chain initialLink).point proof H j.val)).2))

private theorem replay_terminalBody (initialLink : Digest) (proof : Replay.Output g fields Advice Auth)
    (H : Replay.Point g fields Advice Auth Key (Block capacity Fresh) → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) :
    terminalBody ((e.chain initialLink).point proof H n) =
      if n = g.roles.length then some proof.body else none := by
  have hr := (e.chain initialLink).point_rank proof H hn
  have hb := e.replay_body initialLink proof H n
  cases hp : (e.chain initialLink).point proof H n with
  | round i history block =>
      rw [hp] at hr
      change i.val = n at hr
      have hi := i.isLt
      simp only [terminalBody,if_neg (by omega : n ≠ g.roles.length)]
  | finalSeal history body =>
      rw [hp] at hr
      change g.roles.length = n at hr
      have hbody := hb history body hp
      simp only [terminalBody,if_pos hr.symm,hbody]

/-- Every real replay point is a canonical parsed-prefix image once each
round's block is constructed from its public packet producer. No assertion
that all queries are canonical is required. -/
theorem point_eq_replay
    (hblock : ∀ proof i past,
      e.block proof (index packets hroles i) past = (packets.get i).block (producer proof i past))
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth)
    (hbody : (bodyCodec.encode proof.body).length ≤ maxLength)
    (H : Replay.Point g fields Advice Auth Key (Block capacity Fresh) → Digest × C)
    (n : ℕ) (hn : n ≤ packets.length) :
    pointAt bodyCodec packets hroles (e.context proof)
      (replayValues e packets producer initialLink proof H)
      (fun i => (H ((e.chain initialLink).point proof H i.val)).1) ⟨proof.body,hbody⟩ n hn =
        (e.chain initialLink).point proof H n := by
  have hlen : packets.length = g.roles.length := by
    simpa only [List.length_map] using congrArg List.length hroles
  let values := replayValues e packets producer initialLink proof H
  let links : Fin packets.length → Digest := fun i => (H ((e.chain initialLink).point proof H i.val)).1
  let expected := fun n hn => pointAt bodyCodec packets hroles (e.context proof) values links ⟨proof.body,hbody⟩ n hn
  have hrank : ∀ n hn, (expected n hn).rank = n := by
    intro n hn
    exact (reindex_rank hroles _).trans (embed_valueAt_rank bodyCodec packets values links _ n hn _)
  have hrealrank : ∀ n (hn : n ≤ packets.length),
      Input.rank ((e.chain initialLink).point proof H n) = n := by
    intro n hn
    exact (e.chain initialLink).point_rank proof H (by omega)
  have hcontext : ∀ n hn, (expected n hn).context = ((e.chain initialLink).point proof H n).context := by
    intro n hn
    rw [e.point_context]
    exact (reindex_context hroles _).trans (embed_context bodyCodec _ _ _)
  have hblocks : ∀ n hn, (expected n hn).block = ((e.chain initialLink).point proof H n).block := by
    intro n hn
    by_cases hlt : n < packets.length
    · let i : Fin packets.length := ⟨n,hlt⟩
      change (reindex hroles _).block = _
      rw [reindex_block]
      have hb := embed_valueAt_block bodyCodec packets values links ⟨proof.body,hbody⟩ i (e.context proof)
      have hv : Values.get values i = producer proof i
          (fun j => (H ((e.chain initialLink).point proof H j.val)).2) := Values.get_ofFn _ _ _
      rw [hv] at hb
      have ha := e.point_block initialLink proof H (index packets hroles i)
      rw [hblock] at ha
      exact hb.trans ha.symm
    · have he : n = packets.length := by omega
      rw [block_none _ ((hrank n hn).trans (he.trans hlen)),
        block_none _ ((hrealrank n hn).trans (he.trans hlen))]
  have hbodies : ∀ n hn, terminalBody (expected n hn) = terminalBody ((e.chain initialLink).point proof H n) := by
    intro n hn
    change terminalBody (reindex hroles _) = _
    rw [reindex_terminalBody,embed_valueAt_terminalBody]
    rw [replay_terminalBody e initialLink proof H n (by omega),hlen]
  change expected n hn = _
  induction n with
  | zero =>
      refine point_ext initialLink (expected 0 hn) ((e.chain initialLink).point proof H 0)
        ((hrank 0 hn).trans (hrealrank 0 hn).symm) ?_ ?_
        (hcontext 0 hn) (hblocks 0 hn) (hbodies 0 hn)
      · exact (parent_zero _ (hrank 0 hn)).trans (parent_zero _ (hrealrank 0 hn)).symm
      · exact (claimed_zero initialLink _ (hrank 0 hn)).trans
          (claimed_zero initialLink _ (hrealrank 0 hn)).symm
  | succ n ih =>
      have hlt : n < packets.length := by omega
      have hprev := ih (by omega)
      let block := if hnext : n+1 < packets.length then
          (packets.get ⟨n+1,hnext⟩).block (Values.get values ⟨n+1,hnext⟩)
        else (packets.get ⟨n,hlt⟩).block (Values.get values ⟨n,hlt⟩)
      have hstep : expected (n+1) hn = next proof.body block (links ⟨n,hlt⟩) (expected n (by omega)) := by
        change reindex hroles _ = _
        erw [embed_valueAt_succ bodyCodec packets values links _ n hlt _ block
          (by intro h; simp only [block,dif_pos h]),reindex_next]
        rfl
      refine point_ext initialLink (expected (n+1) hn) ((e.chain initialLink).point proof H (n+1))
        ((hrank (n+1) hn).trans (hrealrank (n+1) hn).symm) ?_ ?_
        (hcontext (n+1) hn) (hblocks (n+1) hn) (hbodies (n+1) hn)
      · have hp := next_parent proof.body block (links ⟨n,hlt⟩) (expected n (by omega))
          (by rw [hrank]; omega)
        exact (congrArg Input.parent hstep).trans
          (hp.trans ((congrArg some hprev).trans ((e.chain initialLink).point_parent proof H (by omega)).symm))
      · have hp := next_claimed proof.body block (links ⟨n,hlt⟩) initialLink (expected n (by omega))
          (by rw [hrank]; omega)
        exact (congrArg (Input.claimed initialLink) hstep).trans
          (hp.trans ((e.chain initialLink).point_link proof H (by omega)).symm)

end Replay


namespace Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

local notation "packets" => QueryRuntime.Runtime.packets repr shape setup publicCount

def packetIndex (i : Fin g.roles.length) : Fin (packets).length :=
  Fin.cast (by simpa only [List.length_map] using
    (congrArg List.length (QueryRuntime.Runtime.roles_eq repr shape setup publicCount)).symm) i

def packetAt (i : Fin g.roles.length) := (packets).get (packetIndex repr shape setup publicCount i)

theorem packetAt_zero (i : Fin g.roles.length) (hi : i.val = 0) :
    packetAt repr shape setup publicCount i = QueryRuntime.Runtime.first repr shape setup publicCount := by
  cases i with
  | mk n hn =>
      change n = 0 at hi
      subst n
      rfl

theorem packetAt_pos (i : Fin g.roles.length) (hi : 0 < i.val) :
    packetAt repr shape setup publicCount i = QueryRuntime.Runtime.ordinary repr shape setup publicCount i := by
  rcases i with ⟨n,hn⟩
  change 0 < n at hi
  cases n with
  | zero => omega
  | succ n =>
      simp only [packetAt,packetIndex,QueryRuntime.Runtime.packets,List.get_eq_getElem,Fin.cast_mk,
        List.getElem_cons_succ,List.getElem_tail,List.getElem_ofFn]

private def castData {first second : Packet (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))
    (QueryRuntime.Runtime.capacity repr shape setup publicCount)} (h : first = second) (value : first.Data) : second.Data := h ▸ value

private theorem block_castData {first second : Packet (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))
    (QueryRuntime.Runtime.capacity repr shape setup publicCount)} (h : first = second) (value : first.Data) :
    second.block (castData repr shape setup publicCount h value) = first.block value := by cases h; rfl

/-- The first packet is the context itself. Ordinary packet data is supplied
by the body-and-request constructor at its actual counter. -/
def dataAt (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) : (packetAt repr shape setup publicCount i).Data :=
  if hi : i.val = 0 then castData repr shape setup publicCount
    (packetAt_zero repr shape setup publicCount i hi).symm context
  else castData repr shape setup publicCount
    (packetAt_pos repr shape setup publicCount i (by omega)).symm ordinary

theorem block_dataAt_zero (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) (hi : i.val = 0) :
    (packetAt repr shape setup publicCount i).block (dataAt repr shape setup publicCount context i ordinary) =
      (QueryRuntime.Runtime.first repr shape setup publicCount).block context := by
  simp only [dataAt,dif_pos hi]
  exact block_castData repr shape setup publicCount _ _

theorem block_dataAt_pos (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) (hi : 0 < i.val) :
    (packetAt repr shape setup publicCount i).block (dataAt repr shape setup publicCount context i ordinary) =
      (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block ordinary := by
  simp only [dataAt,dif_neg (by omega : i.val ≠ 0)]
  exact block_castData repr shape setup publicCount _ _


/-- A packet factory makes every verifier replay input canonical, including
the complete-proof final seal. Only a static public size bound is required
for framing that last body. The two block identities are constructor
identities, not a semantic acceptance or canonicality certificate. -/
theorem canonical_of_blocks {C : Type}
    (e : Replay.Encoding g fields Advice (OpeningBody.Authentication g)
      (FingerprintPrefix.Key publicCount)
      (Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
        (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))) C)
    (ordinary : Replay.Output g fields Advice (OpeningBody.Authentication g) →
      (i : Fin g.roles.length) → (Fin i.val → C) → WireBlocks.Data (Advice := Advice) shape i)
    (hzero : ∀ proof i past, i.val = 0 → e.block proof i past =
      (QueryRuntime.Runtime.first repr shape setup publicCount).block (e.context proof))
    (hpos : ∀ proof i past, 0 < i.val → e.block proof i past =
      (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block (ordinary proof i past))
    (hfits : ProofBodyBounds.bodyBound repr g ≤ maxLength)
    (initialLink : Digest) (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
    (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) :
    QueryRuntime.Runtime.Canonical repr shape setup publicCount ((e.chain initialLink).point proof H n) := by
  let roles := QueryRuntime.Runtime.roles_eq repr shape setup publicCount
  let producer := fun (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
      (ip : Fin (packets).length) (past : Fin ip.val → C) =>
    dataAt repr shape setup publicCount (e.context proof) (index (packets) roles ip)
      (ordinary proof (index (packets) roles ip) past)
  have hblocks : ∀ proof ip past,
      e.block proof (index (packets) roles ip) past =
        ((packets).get ip).block (producer proof ip past) := by
    intro proof ip past
    let i := index (packets) roles ip
    change e.block proof i past =
      (packetAt repr shape setup publicCount i).block
        (dataAt repr shape setup publicCount (e.context proof) i (ordinary proof i past))
    by_cases hi : i.val = 0
    · rw [block_dataAt_zero repr shape setup publicCount _ _ _ hi]
      exact hzero proof i past hi
    · rw [block_dataAt_pos repr shape setup publicCount _ _ _ (by omega : 0 < i.val)]
      exact hpos proof i past (by omega)
  have hlen : (packets).length = g.roles.length := by
    simpa only [List.length_map] using congrArg List.length roles
  have hn' : n ≤ (packets).length := by omega
  have hbody := ProofBodyBounds.final_fits repr g hfits proof.body
  let values := replayValues e (packets) producer initialLink proof H
  let value := valueAt (ProofBodyCodec.codec repr g) (packets) values
    (fun i => (H ((e.chain initialLink).point proof H i.val)).1) ⟨proof.body,hbody⟩ n hn'
  have hkey : QueryRuntime.Runtime.key repr shape setup publicCount value = e.context proof := by
    cases n <;> rfl
  refine ⟨value,?_⟩
  change reindex roles (embed (ProofBodyCodec.codec repr g)
    (QueryRuntime.Runtime.key repr shape setup publicCount value) (packets) value) = _
  rw [hkey]
  exact point_eq_replay e (ProofBodyCodec.codec repr g) (packets) roles producer hblocks
    initialLink proof hbody H n hn'

end Runtime

end LfzkV2.Current.CanonicalReplay
