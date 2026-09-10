
184
18 Merkle commitment scheme
We describe theMerkle commitment scheme, a commitment scheme in the ROM that produces
succinct commitments to long lists of values and enables cheaply opening particular subsets
of values in the list. This useful “succinct opening” property is used to construct succinct
arguments in the ROM.
1
The commitment scheme is so-called because it relies on Merkle
trees [Mer89a], a powerful and versatile data structure based on hash functions. A Merkle
commitment scheme uses the basic commitment schemeCMas a building block, so throughout
this chapter we assume familiarity with the material in Chapter 17.
OrganizationIn Section 18.1 we describe the construction of a Merkle commitment scheme,
and discuss its efficiency properties. Then in Section 18.2 we discuss itscompleteness property,
that is, how an honest use of the commitment scheme always leads to successful validity checks.
After that we discuss security properties. In Section 18.3 we establish a technical property that
we use in several security analyses. After that we discuss the main security properties of a
Merkle commitment scheme:
•in Section 18.4 we prove thatMTisbinding;
•in Section 18.5 we prove thatMTisextractable;
•in Section 18.6 we prove thatMTishiding;
•in Section 18.7 we prove thatMTisequivocable.
18.1 Definition
AMerkle commitment schemeis a tuple of three algorithms:
MT=(MT.Commit,MT.Open,MT.Check).
The scheme has several parameters: an output size
alphabet⌃, a message length`, and a salt sizesPN. We use the notationMT[
we wish to make these parameters explicit.
The algorithms receive query access to a random oraclefPU
b
(
syntax.
•Commit.The algorithmMT.Commitreceives as input a message vectormP⌃
`
, and
computes a Merkle commitmentrtPt0,1u

and corresponding opening trapdoortdP
t0,1u
O((s+
. This algorithm is probabilistic if privacy is desired (otherwise it is deter-
ministic).
1
More generally, succinct commitments with succinct opening are known asvector commitmentsin the cryptography
literature, and constructions are known from various cryptographic assumptions. They are used to construct
succinct arguments in various settings also beyond the (pure) ROM.

18 Merkle commitment scheme185
•Open.The algorithmMT.Openreceives as input opening trapdoortdand a subsetIÑ[`],
and computes an opening proofpfthat authenticates the values at the locations inI.
•Check.The algorithmMT.Checkreceives as input a Merkle commitmentrt, subsetIÑ[`],
claimed valuesaP⌃
I
, and opening proofpf, and computes a bit indicating whether the
opening proofpfauthenticatesaas values for the locations inIwith respect tort.
Henceforth we assume that`is a power of2; see Remark 18.1.7 for a discussion of how to
remove this assumption.
Binary treeWe introduce notation for a (perfect) binary tree on`leaves,
2
which then we use
to describe the algorithms of the Merkle commitment scheme. Those algorithms can be viewed
as labeling (or checking the labels of) vertices of this (perfect) binary tree.
Definition 18.1.1.For`PN,T
`
=(V
`
,E
`
)is the (perfect)binary tree graphof depth
d
:
=log
2
`(18.1)
where the vertex setV
`
and edge setE
`
are defined as follows:
V
`
:
=

(j, i):jPt0,1,...,du,iP[2
j
]
(
,
E
`
:
=


(j ́1,i),(j,2i ́b)

:jPt1,...,du,iP[2
j ́1
],bPt1,0u
(
.
We use the depthdthroughout this chapter without explicitly re-defining it as in Equa-
tion 18.1.
Definition 18.1.2.We make the following notational definitions:
•Theroot vertexofT
`
is the vertex(0,1).
•Theleaf verticesofT
`
are the verticest(d, i)u
iP[`]
.
•A vertex(j, i)isoddifiis odd and it isevenifiis even.
•Thesiblingof a non-root vertex(j, i)(i.e., withj°0) is(j, i+ 1)if(j, i)is odd and is
(j, i ́1)if(j, i)is even.
•Thepathfrom thei-th leaf vertex(d, i)to the root vertex is denoted bypath(i); the vertex
inpath(i)that is in layerjis denotedp(i, j)Ptjuˆ[2
j
].
•Thecopathfrom thei-th leaf vertex(d, i)to the root vertex is denoted bycopath(i), and is
the list of siblings of each vertex inpath(i), except the root vertex (which has no siblings);
the vertex incopath(i)that is in layerjis denoted
 ̄
p(i, j)Ptjuˆ[2
j
](and is the sibling of
p(i, j)).
•ForIÑ[`],path(I)
:
=
Y
iPI
path(i)andcopath(I)
:
=
Y
iPI
copath(i)(viewing lists as sets).
Using this notation we can write:
path(i)=
⇣
p(i, j)
⌘
jPt0,1,...,du
andcopath(i)=
⇣
 ̄
p(i, j)
⌘
jPt1,...,du
.
For everyiP[`],p(i,0) = (0,1)is the root vertex andp(i, d)=(d, i)is thei-th leaf.
2
A binary tree isperfectif all internal vertices have two children and all leaf vertices belong to the same layer.

18 Merkle commitment scheme186
root
leaves
layer 0
layer 1
layer 2
layer 3
odd
oddeven
oddoddoddoddeveneveneveneven
oddoddeveneven
(3,1)(3,2)(3,3)(3,4)
(2,1)(2,2)
(1,1)
(3,5)
(3,6)(3,7)(3,8)
(2,3)
(2,4)
(1,2)
(0,1)
Figure 18.1:Diagram of the binary tree graphT
8
. The vertices highlighted in yellow arepath(6) =

(3,6),(2,3),(1,2),(0,1)

and the vertices highlighted in blue arecopath(6) =

(3,5),(2,4),(1,1)

. For example, p(6,1) = (1,2)and
 ̄
p(6,1) = (1,1).
ConstructionWe describe each of the algorithms in the Merkle commitment schemeMT.
•MT.Commit
f
(m)Ñ(rt,td)
1.For each message locationi=1,...,`:
–sample a salt⌧
i
Pt0,1u
s
;
–compute the (hiding) commitmentc
(d,i)
:
=f(m[i],⌧
i
)Pt0,1u

.
2.For each layerj=d ́1,...,0and for eachi=1,...,2
j
:
–compute the (non-hiding) commitmentc
(j,i)
:
=f(c
(j+1,2i ́1)
,c
(j+1,2i)
)Pt0,1u

.
3.Set the Merkle commitmentrt
:
=c
(0,1)
.
4.Set the salts⌧
:
=(⌧
i
)
iP[`]
.
5.Set the commitmentsC
:
=((c
(j,i)
)
iP[2
j
]
)
d
j=0
, which we can visualize in the following way:
C=
2
6
6
6
6
6
4
c
(0,1)
c
(1,1)
c
(1,2)
c
(2,1)
c
(2,2)
c
(2,3)
c
(2,4)
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
c
(d,1)
.........   ...  c
(d,2
d
)
3
7
7
7
7
7
5
.
6.Set the opening trapdoortd
:
=(⌧,C).
7.Output(rt,td).
Informally, this algorithm first commits to each message entry via a basic commitment
scheme (the one discussed in Chapter 17) and labels the leaves of the binary tree with these
commitments, and then recursively labels every vertex in the tree with the hash of the labels
of its two children.
•MT.Open
f
(td,I)Ñpf
1.For everyiPI, set the authentication path for locationi:
auth
i
:
=

⌧
i
,(c
 ̄
p(i,j)
)
jPt1,...,du

.(18.2)
2.Output the opening proofpf
:
=(auth
i
)
iPI
.
Informally, this algorithm includes an authentication path for each opened location. An
authentication for a location includes the salt for that location, as well as the values assigned
to siblings of vertices from that leaf location to the root.

18 Merkle commitment scheme187
•MT.Check
f
(rt,I,a,pf)Ñb
1.Parsepfas(auth
i
)
iPI
.
2.For everyiPI, check thatauth
i
authenticates the valuea[i]P⌃as thei-th opening
relative to the Merkle commitmentrtPt0,1u

by computing(c
p(i,j)
)
jPt0,1,...,du
:
a)compute the commitmentc
(d,i)
:
=f(a[i],⌧
i
);
b)compute the commitments(c
p(i,j)
)
jPt0,1,...,d ́1u
as follows:
for each layerj=d ́1,...,1,0:
–ifp(i, j+ 1)is an odd vertex then setc
L
:
=c
p(i,j+1)
andc
R
:
=c
 ̄
p(i,j+1)
;
–ifp(i, j+ 1)is an even vertex then setc
L
:
=c
 ̄
p(i,j+1)
andc
R
:
=c
p(i,j+1)
;
–compute the commitmentc
p(i,j)
:
=f(c
L
,c
R
).
c)check thatrt=c
(0,1)
.
Informally, this algorithm checks the authentication path from each location. Checking
an authentication path involves re-computing the values assigned to vertices from the leaf
vertex of the location to the root vertex, and checking that the resulting root value equals
the given Merkle commitment. Note that
MT.Check
f
(rt,I,a,pf)=
^
iPI
MT.Check
f
(rt,i,a[i],auth
i
).(18.3)
Above we slightly abuse notation in that we drop the set notation whenMT.Checkreceives
a single location and a single corresponding authentication path.
EfficiencyWe discuss the efficiency of each algorithm.
•The algorithmMT.Commitmakes`queries of sizelog
|
⌃
|
+s, and
∞
jP[d]
`/2
d ́j ́1
§`
queries of size2
has sizes`+2`
•The algorithmMT.Openmakes no oracle calls, and simply includes in the opening proof
an authentication path for each index in the setI. An authentication path has size
s+d
|
I
|
 ̈(s+d
size of an opening proof.
•The algorithmMT.Check, for each location in the setI, makes one query of sizelog
|
⌃
|
+s
anddqueries of size2
|
Y
iPI
path(i)
|
(there may be
duplicates).
Remark 18.1.3(no privacy).If no privacy is desired then the construction ofMTsimplifies
as follows: (i)s=0(no salts are sampled); (ii) inMT.Commit, setc
(d,i)
:
=m[i]for eachiP[`]
(instead of committing first by settingc
(d,i)
:
=f(m[i],⌧
i
)) and then the opening trapdoortd
does not include any salts; (iii) inMT.Open, each authentication pathauth
i
does not include
any salt; (iv) inMT.Check, similarly toMT.Commit, simply setc
(d,i)
:
=m[i]for eachiPI(in
Item 2a). The efficiency measures are correspondingly reduced by settings=0.
Remark 18.1.4(recomputing the tree).Some information fromtdcan be omitted (thereby
reducing its size) at the expense of additional computation byMT.Open. Specifically, the
commitments((c
(j,i)
)
iP[2
j
]
)
d ́1
j=1
in the opening trapdoortdcan be derived via at most`random

18 Merkle commitment scheme188
leaf commitments
m
1
, 푥
1
m
2
, 푥
2
m
3
, 푥
3
m
4
, 푥
4
m
5
, 푥
5
m
6
, 푥
6
m
7
, 푥
7
m
8
, 푥
8
c
(3,1)
c
(3,2)
c
(3,3)
c
(3,4)
c
(3,5)
c
(3,6)
c
(3,7)
c
(3,8)
c
(2,1)
c
(2,2)
c
(2,3)
c
(2,4)
c
(1,1)
c
(1,2)
c
(0,1)
Merkle commitment
message entries
and salts
푦푦푦푦푦푦푦푦
푦푦푦푦
푦푦
푦
Figure 18.2:Diagram of the computation inMT.Committo produce a Merkle commitment for a
message of length`=8. Moreover, highlighted in blue is the information included in
an opening proofpffor the6-th entry of the message (which is highlighted in yellow):
the salt⌧
6
and the commitments(c
(3,5)
,c
(2,4)
,c
(1,1)
)that correspond to the copath
copath(6) =

(3,5),(2,4),(1,1)

.
oracle calls from the commitments(c
(d,i)
)
iP[`]
, and thus could be omitted fromtd. In such a
case,MT.Openwould have to query the random oracle to (re)derive the commitments required
to construct the relevant authentication paths. In fact,(c
(d,i)
)
iP[`]
can themselves be derived
from the messagemand salts⌧via`random oracle calls; so one could even settd
:
=(m,⌧),
which may be advantageous iflog
|
⌃
|
is smaller than
tradeoffs in practice.
Remark 18.1.5(local updates).Merkle commitments arelocally updatable, which is a useful
feature in many applications (though we do not explore it further within the context of succinct
arguments). Suppose you are given a Merkle commitmentrtof a messagem, and you want to
update it to be a Merkle commitmentrt
1
of a messagem
1
wherem
1
is equal tomexcept for the
i-th entry. There is no need to recompute the tree from scratch: one only needs to recompute
the commitments for the vertices on the pathpath(i), while the other commitments remain
unchanged. The work needed for this update is proportional to the depth of the tree (which is
logarithmic in the message length) rather than the message length.
Remark 18.1.6(`=1).The message length`=1is a power of2, and in this case the binary
treeT
`
contains a single vertex, the root vertex. In this degenerate case (`=1) the Merkle
commitmentMThappens to equal the basic commitmentCM.
Remark 18.1.7(any message length).The description of the Merkle commitment schemeMT
given above involves a binary tree over`leaves, where`is the number of entries in the message
vector. Notationally it is far simpler to describe and analyze the case when`is a power of2
(which we assume throughout this chapter) because the internal vertices in the binary tree can
be labeled via a simple naming scheme and, more generally, all paths from the root vertex to a

18 Merkle commitment scheme189
leaf vertex “look the same”. But how do Merkle commitment schemes work when`is not a
power of2?
One option is to pad the message with dummy values (an arbitrary symbol from the alphabet
⌃) until the padded message length reaches a power of2; this, at most, doubles the length
relative to the original (unpadded) message. All security analyses of this chapter hold for the
padded message, and in particular for the original (unpadded) message.
While the padding is not expensive, there are cheaper solutions that involve binary trees with
precisely`leaves (without using any padding). This optimization is explained in Section 29.1.
Remark 18.1.8(other arities).The description above involves a perfectbinarytree. However
the construction of a Merkle commitment scheme and the properties that we study (completeness,
binding, extractability, hiding) directly extend to perfect trees of any arity. (In fact, see
Section 29.1 for ageneralizedMerkle commitment scheme that is defined forany tree.) If the
tree has aritya•2then each authentication path containsa ́1vertices per layer rather than
1, and the number of layers in the tree islog
a
`rather thanlog
2
`. Larger arities are usually
not advantageous for the size of opening proofs (the tree has fewer layers but there are more
sibling vertices for an overall bigger opening proof size), though there may be other reasons to
consider trees of higher arity (e.g., fewer calls to the random oracle).
18.2 Completeness
We prove thatMT.Commithascompleteness, namely, if the algorithms of the Merkle commitment
scheme are used as intended then validity checks always pass. In more detail,MT.Commitcan
be used to commit to any message vector, andMT.Opencan be used to open any subset of
locations of the message vector in such a way that the resulting opening proof is accepted by
MT.Check.
Lemma 18.2.1(MTis complete).LetMT
:
=MT[
Pr
2
6
6
4
MT.Check
f
(rt,I,m[I],pf)=1
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(m,I)–A
f
(rt,td)–MT.Commit
f
(m)
pf–MT.Open
f
(td,I)
3
7
7
5
=1.
A formal proof of this lemma would involve analyzing each step of each Merkle commitment
algorithm in order to establish that all validity checks pass. This would not provide useful
insights. Instead we sketch the proof at high level to provide the main intuition.
Fix an arbitrary choice of oraclefPU
b
(
`
, and subsetIÑ[`].
The algorithmMT.Commitcomputes the Merkle commitment formby first committing to
each entry ofm(using a random salt⌧
i
for each message entrym[i]), then pairwise hashes the
resulting list to halve its size, and so on, until it obtains a single outputrt; the trapdoortdis
set to contain all the salts that were sampled and all the commitmentsC
:
=((c
(j,i)
)
iP[2
j
]
)
d
j=0
that were computed.
Subsequently, the algorithmMT.Openincludes in the opening proofpfan authentication
pathauth
i
=

⌧
i
,(c
 ̄
p(i,j)
)
jPt1,...,du

for each indexiin the subsetI.
The algorithmMT.Check, for each indexiin the subsetI, checks that the authentication
pathauth
i
is valid relative to the Merkle commitmentrt, indexi, and valuea[i]. The check for

18 Merkle commitment scheme190
each authentication path succeeds becauseMT.Openconstructed that path by including the
correct salt and the correct commitments, which will leadMT.Checkto recompute the same
value for the root vertex asrt.
18.3 Collision lemma
We formulate and prove acollision lemmafor Merkle commitments, which is a basic security
property that we use in later sections. Informally, the lemma states that authenticating different
values for the same leaf in a Merkle commitment leads to a collision in the random oracle.
Stating this property precisely, however, requires some care. The discussion below takes an
incremental approach by considering simpler types of collision lemmas. First, we describe a
collision lemma for the basic commitment schemeCMin Chapter 17. Second, we describe a
special case of the collision lemma for Merkle commitment schemes. Third, and finally, we
describe the (general) collision lemma for Merkle commitment schemes.
Starting simple: collisions inCMConsider the basic commitment schemeCMin Chapter 17,
whose checking algorithmCM.Checksimply consists of checking a query-answer pair of the
random oracle:CM.Check
f
(cm,m,⌧)=1if and only ifcm=f(m,⌧). Consider a commitment
cmand two message-salt pairs,(m
0
,⌧
0
)and(m
1
,⌧
1
). Suppose that both pairs are valid openings
of the commitment, that is,CM.Check
f
(cm,m
0
,⌧
0
)=1andCM.Check
f
(cm,m
1
,⌧
1
)=1. By the
definition ofCM.Check, these conditions are equivalent tocm=f(m
0
,⌧
0
)andcm=f(m
1
,⌧
1
),
from which we deduce thatf(m
0
,⌧
0
)=f(m
1
,⌧
1
). This tells us that if eitherm
0
‰m
1
(the
messages are distinct) or⌧
0
‰⌧
1
(the salts are distinct) then the two executions ofCM.Check
on the two inputs result in a collision forf. Thus, inCM,opening the same commitment either
via two different messages or via two different salts leads to a collision. We can summarize this
property as a “collision lemma forCM” via the following implication:
2
4

m
0
‰m
1
_⌧
0
‰⌧
1

^CM.Check
f
(cm,m
0
,⌧
0
)=1
^CM.Check
f
(cm,m
1
,⌧
1
)=1
3
5
ñ

(m
0
,⌧
0
)and(m
1
,⌧
1
)
are a collision forf

.
What aboutMT?We wish to derive a similar lemma for the Merkle commitment scheme
MT. The challenge is that messages inMTcan be opened at subsets of locations (rather than
only at all locations), which complicates the assumptions under which a collision can be proved
to exist. Moreover, the algorithmMT.Check, which validates the corresponding opening proofs,
involves a more complex computation. In particular, the computation involves multiple queries
to the random oracle (rather than one query as inCM), and arguing that a collision exists in
the relevant query-answer traces will involve a delicate case analysis. We tackle this additional
complexity by first analyzing a special case and then analyzing the general case.
Special case: opening a single leafAs a warmup we consider the special case where we
only consider opening proofs for a single leaf. In other words, we consider computations for
MT.Check
f
(rt,I,a,pf)where the setI=tiuis a singleton and so: (i)ais a vector consisting of
a single entrymin⌃; and (ii)pfconsists of a single authentication pathauth.
Consider a Merkle commitmentrtand positioniP[`], and two openings: a claimed value
m
0
P⌃and corresponding authentication pathauth
0
, and another claimed valuem
1
P⌃

18 Merkle commitment scheme191
and corresponding authentication pathauth
1
. Suppose that both openings are valid, that is,
MT.Check
f
(rt,i,m
0
,auth
0
)=1andMT.Check
f
(rt,i,m
1
,auth
1
)=1. Intuitively, since the two
computations share the same Merkle commitmentrt, ifm
0
‰m
1
then the two random oracle
computations “collide” at some layer of the binary tree in order to eventually lead to the same
Merkle commitmentrtat the root of the tree. The collision is either at a leaf commitment,
or at an internal commitment; see Figure 18.3 for an example. In fact, we can prove that the
same is true even ifm
0
=m
1
andauth
0
‰auth
1
.
m
6
(0)
, 푥
6
(0)
m
6
(1)
, 푥
6
(1)
c
(3,5)
c
(3,6)
c
(2,3)
c
(2,4)
c
(1,1)
c
(1,2)
c
(0,1)
푦푦
푦
푦
푦
(a)
m
6
(0)
, 푥
6
(0)
c
(3,5)
(0)
c
(3,6)
(0)
c
(2,3)
(0)
c
(2,4)
(0)
c
(1,1)
c
(1,2)
c
(0,1)
푦
푦
푦
푦
m
6
(1)
, 푥
6
(1)
c
(3,5)
(1)
c
(3,6)
(1)
c
(2,3)
(1)
c
(2,4)
(1)
푦
푦
푦
(b)
Figure 18.3:Example of a collision for two paths that authenticate two different values for the
6-th entry (out of8entries). There are two cases: in the left, a collision at a leaf
commitment; and, on the right, a collision at an internal commitment.
More precisely, the collision involves a query from the query-answer traceS
0
of the computa-
tionMT.Check
f
(rt,i,m
0
,auth
0
)and a query from the query-answer traceS
1
of the computation
MT.Check
f
(rt,i,m
1
,auth
1
).
Note that here it is necessary for the two openings to be about the same positioni. This
is because it is possible to open two different positions via two different values (or different
authentication paths) without causing collisions. Indeed, this would happen for most choices of
random oracle for a message with different values.
We formally state and prove this below.
Lemma 18.3.1.LetMT
:
=MT[
b
(
Merkle commitmentrtPt0,1u

; an indexiP[`]; message entriesm
0
,m
1
P⌃; and authentication
pathsauth
0
,auth
1
. ForbPt0,1u, letS
b
be the query-answer trace ofMT.Check
f
(rt,i,m
b
,auth
b
).
Then the following implication holds:
2
4

m
0
‰m
1
_auth
0
‰auth
1

^MT.Check
f
(rt,i,m
0
,auth
0
)=1
^MT.Check
f
(rt,i,m
1
,auth
1
)=1
3
5
ñ

D(x
0
,y
0
)PS
0
,(x
1
,y
1
)PS
1
withx
0
‰x
1
such thaty
0
=y
1

.(18.4)

18 Merkle commitment scheme192
Proof.FixbPt0,1u. The authentication pathauth
b
for indexihas the following structure:
auth
b
=
⇣
⌧
(b)
i
,(c
(b)
 ̄
p(i,j)
)
jPt1,...,du
⌘
,
where⌧
(b)
i
is a Merkle salt and(c
(b)
 ̄
p(i,j)
)
jPt1,...,du
are commitments labeling vertices incopath(i).
Moreover, the computationMT.Check
f
(rt,i,m
b
,auth
b
)leads to a query-answer traceS
b
consisting ofd+1query-answer pairs. The answers inS
b
are denoted
(c
(b)
p(i,j)
)
jPt0,1,...,du
.
Finally,MT.Check
f
(rt,i,m
b
,auth
b
)=1implies thatrt=c
(b)
(0,1)
.
In particular, we deduce thatc
(0)
(0,1)
=c
(1)
(0,1)
.
We consider two cases.
•Case 1: there existsjP[d]such thatc
(0)
p(i,j)
‰c
(1)
p(i,j)
orc
(0)
 ̄
p(i,j)
‰c
(1)
 ̄
p(i,j)
.
Letjbe the minimal index satisfying this condition.
–Ifp(i, j)is an odd vertex then forbPt0,1uset(c
(b)
L
,c
(b)
R
)
:
=(c
(b)
p(i,j)
,c
(b)
 ̄
p(i,j)
).
–Ifp(i, j)is an even vertex then forbPt0,1uset(c
(b)
L
,c
(b)
R
)
:
=(c
(b)
 ̄
p(i,j)
,c
(b)
p(i,j)
).
ForbPt0,1uthe pair(c
(b)
L
,c
(b)
R
)is a query inS
b
(see Item 2b in the description of
MT.Check).
These two queries are a collision forfdue to the following.
–(c
(0)
L
,c
(0)
R
)‰(c
(1)
L
,c
(1)
R
).
This follows sincec
(0)
p(i,j)
‰c
(1)
p(i,j)
orc
(0)
 ̄
p(i,j)
‰c
(1)
 ̄
p(i,j)
.
–f(c
(0)
L
,c
(0)
R
)=f(c
(1)
L
,c
(1)
R
).
This follows sincec
(0)
p(i,j ́1)
=f(c
(0)
L
,c
(0)
R
),c
(1)
p(i,j ́1)
=f(c
(1)
L
,c
(1)
R
), andc
(0)
p(i,j ́1)
=
c
(1)
p(i,j ́1)
. The last equality holds becausejis the minimal index satisfying the condition
(and we know thatc
(0)
(0,1)
=c
(1)
(0,1)
).
•Case 2:c
(0)
(d,i)
=c
(1)
(d,i)
, andm
0
‰m
1
or⌧
(0)
i
‰⌧
(1)
i
.
ForbPt0,1uthe pair(m
b
,⌧
(b)
i
)is a query inS
b
(see Item 2a in the description of
MT.Check).
These two queries are a collision forfdue to the following.
–(m
0
,⌧
(0)
i
)‰(m
1
,⌧
(1)
i
). This follows sincem
0
‰m
1
or⌧
(0)
i
‰⌧
(1)
i
.
–f(m
0
,⌧
(0)
i
)=f(m
1
,⌧
(1)
i
). This follows sincec
(0)
(d,i)
=f(m
0
,⌧
(0)
i
),c
(1)
(d,i)
=f(m
1
,⌧
(1)
i
),
andc
(0)
(d,i)
=c
(1)
(d,i)
.
In either case we find a collision with one query inS
0
and the other query inS
1
.
We are left to argue that the antecedent in Equation 18.4 implies that Case 1 or Case 2 holds.
If Case 1 holds then we are done. So suppose that Case 1 does not hold, which means that
(c
(0)
p(i,j)
)
jP[d]
=(c
(1)
p(i,j)
)
jP[d]
and(c
(0)
 ̄
p(i,j)
)
jP[d]
=(c
(1)
 ̄
p(i,j)
)
jP[d]
(and in particular thatc
(0)
(d,i)
=c
(1)
(d,i)
). If
m
0
‰m
1
then Case 2 holds. Suppose instead thatauth
0
‰auth
1
. The only way for the two
authentication paths to differ in this case is for the Merkle salts to differ (⌧
(0)
i
‰⌧
(1)
i
), in which
case again Case 2 holds.

18 Merkle commitment scheme193
General case: opening multiple leavesWe now consider the collision lemma for the general
case, where opening proofs may authenticate multiple leaves. Consider a Merkle commitmentrt,
as well as: two index setsI
0
,I
1
; two vectorsa
0
,a
1
; two opening proofspf
0
,pf
1
. Suppose that both
openings are valid, that is,MT.Check
f
(rt,I
0
,a
0
,pf
0
)=1andMT.Check
f
(rt,I
1
,a
1
,pf
1
)=1.
Intuitively, and similarly to the case of a single leaf, if there is a positioniPI
0
XI
1
such
thata
0
[i]‰a
1
[i]then we can find a collision in (the union of the relevant) query-answer traces.
Informally, the prior argument works applied to the authentication paths for the indexiin the
opening proofspf
0
andpf
1
(and the subset of query-answer pairs used to validate these paths).
Less obvious is the fact that we cannot expect (in general) to find a collision ifpf
0
‰pf
1
.
This is because the two opening proofs are for potentially different index setsI
0
andI
1
, so the
opening proofs can be different. Nevertheless, we can prove that if the opening proofs are for
the same index set (I
0
=I
1
) and they are different (pf
0
‰pf
1
) then we can find a collision.
We formally state and prove this below.
Lemma 18.3.2.LetMT
:
=MT[
b
(
•a Merkle commitmentrtPt0,1u

;
•a setI
0
Ñ[`], vectora
0
P⌃
I
0
, and opening proofpf
0
;
•a setI
1
Ñ[`], vectora
1
P⌃
I
1
, and opening proofpf
1
.
ForbPt0,1u, letS
b
be the query-answer trace ofMT.Check
f
(rt,I
b
,a
b
,pf
b
). Then the following
implication holds:
2
6
6
6
6
4
0
@
DiPI
0
XI
1
:a
0
[i]‰a
1
[i]
or
I
0
=I
1
^pf
0
‰pf
1
1
A
^MT.Check
f
(rt,I
0
,a
0
,pf
0
)=1
^MT.Check
f
(rt,I
1
,a
1
,pf
1
)=1
3
7
7
7
7
5
ñ

D(x
0
,y
0
)PS
0
,(x
1
,y
1
)PS
1
withx
0
‰x
1
such thaty
0
=y
1

.(18.5)
Proof.FixbPt0,1u. The opening proofpf
b
for the setI
b
has the following structure:
pf
b
=
⇣
⌧
(b)
i
,(c
(b)
 ̄
p(i,j)
)
jPt1,...,du
⌘
iPI
b
.
Above, the value⌧
(b)
i
is the Merkle salt used to authenticate leafi, and the values(c
(b)
 ̄
p(i,j)
)
jPt1,...,du
are the commitments labeling vertices incopath(i)used to authenticate leafi.
Moreover, the computationMT.Check
f
(rt,I
b
,a
b
,pf
b
)obtains as answers fromfthe commit-
ments corresponding to vertices inpath(i). We denote these commitments as
(c
(b)
p(i,j)
)
jPt0,1,...,du
.
Finally,MT.Check
f
(rt,I
b
,a
b
,pf
b
)=1implies thatrt=c
(b)
(0,1)
.
In particular, we deduce thatc
(0)
(0,1)
=c
(1)
(0,1)
.
We consider two cases.
1.Case 1: there existiPI
0
XI
1
andjP[d]such thatc
(0)
p(i,j)
‰c
(1)
p(i,j)
orc
(0)
 ̄
p(i,j)
‰c
(1)
 ̄
p(i,j)
.
Letjbe the minimal index satisfying this condition (for an arbitrary choice ofi).
•Ifp(i, j)is an odd vertex then forbPt0,1uset(c
(b)
L
,c
(b)
R
)
:
=(c
(b)
p(i,j)
,c
(b)
 ̄
p(i,j)
).
•Ifp(i, j)is an even vertex then forbPt0,1uset(c
(b)
L
,c
(b)
R
)
:
=(c
(b)
 ̄
p(i,j)
,c
(b)
p(i,j)
).

18 Merkle commitment scheme194
ForbPt0,1uthe pair(c
(b)
L
,c
(b)
R
)is the query inS
b
(see Item 2b in the description of
MT.Check).
These two queries are a collision forfdue to the following.
•(c
(0)
L
,c
(0)
R
)‰(c
(1)
L
,c
(1)
R
).
This follows sincec
(0)
p(i,j)
‰c
(1)
p(i,j)
orc
(0)
 ̄
p(i,j)
‰c
(1)
 ̄
p(i,j)
.
•f(c
(0)
L
,c
(0)
R
)=f(c
(1)
L
,c
(1)
R
).
This follows sincec
(0)
p(i,j ́1)
=f(c
(0)
L
,c
(0)
R
),c
(1)
p(i,j ́1)
=f(c
(1)
L
,c
(1)
R
), andc
(0)
p(i,j ́1)
=
c
(1)
p(i,j ́1)
. The last equality holds becausejis a minimal index satisfying the condition
for this choice ofi(and we know thatc
(0)
(0,1)
=c
(1)
(0,1)
).
2.Case 2:  there existsiPI
0
XI
1
such thatc
(0)
(d,i)
=c
(1)
(d,i)
and such thata
0
[i]‰a
1
[i]or
⌧
(0)
i
‰⌧
(1)
i
.
ForbPt0,1uthe pair(a
b
[i],⌧
(b)
i
)is a query inS
b
(see Item 2a in the description of
MT.Check).
These two queries are a collision forfdue to the following.
•(a
0
[i],⌧
(0)
i
)‰(a
1
[i],⌧
(1)
i
).
This follows sincea
0
[i]‰a
1
[i]or⌧
(0)
i
‰⌧
(1)
i
.
•f(a
0
[i],⌧
(0)
i
)=f(a
1
[i],⌧
(1)
i
).
This follows sincec
(0)
(d,i)
=f(a
0
[i],⌧
(0)
i
),c
(1)
(d,i)
=f(a
1
[i],⌧
(1)
i
), andc
(0)
(d,i)
=c
(1)
(d,i)
.
In either case we find a collision with one query inS
0
and the other query inS
1
.
We are left to argue that the antecedent in Equation 18.5 implies that Case 1 or Case 2 holds.
Suppose that there existsiPI
0
XI
1
such thata
0
[i]‰a
1
[i]. One of the following must hold.
•If there existsjP[d]such thatc
(0)
p(i,j)
‰c
(1)
p(i,j)
, then Case 1 holds.
•If instead(c
(0)
p(i,j)
)
jP[d]
=(c
(1)
p(i,j)
)
jP[d]
, then in particularc
(0)
(d,i)
=c
(1)
(d,i)
and so Case 2 holds.
Alternatively, suppose thatI
0
=I
1
andpf
0
‰pf
1
. If Case 1 holds then we are done. So
suppose that Case 1 does not hold; in particular we know that(c
(0)
 ̄
p(i,j)
)
jP[d]
=(c
(1)
 ̄
p(i,j)
)
jP[d]
. If so,
the only way forpf
0
‰pf
1
to hold is that there existsiPI
0
XI
1
such that⌧
(0)
i
‰⌧
(1)
i
. Moreover
for thisiwe know thatc
(0)
(d,i)
=c
(1)
(d,i)
because Case 1 does not hold. Hence Case 2 holds.
18.4 Binding
The basic security property of the Merkle commitment scheme is that it isbinding: a Merkle
commitment cannot be opened at the same locations to different values, regardless of the
Merkle opening proofs. In more detail, the probability, over the choice of random oracle, that
an adversary succeeds in this task is small relative to its query complexity. The salt sizes
does not play any role in this property, and in particular it could be zero. This property is
analogous to the one that we studied for the basic commitment schemeCMin Chapter 17 (see
Lemma 17.1.1 in Section 17.1).

18 Merkle commitment scheme195
Later sections actually rely on a stronger property known as extractability, which we discuss
in Section 18.5. Nevertheless, it is useful to understand binding first in order to familiarize
oneself with the basic structure of the Merkle commitment scheme.
Lemma 18.4.1(MTis binding).LetMT
:
=MT[
:
=log
2
`.  For every
query boundtPNandt-query algorithmA,
Pr
2
4
DiPI
0
XI
1
s.t.a
0
[i]‰a
1
[i]
^MT.Check
f
(rt,I
0
,a
0
,pf
0
)=1
^MT.Check
f
(rt,I
1
,a
1
,pf
1
)=1
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,I
0
,a
0
,pf
0
,I
1
,a
1
,pf
1
)–A
f
3
5
§✏
MT
(
Above,✏
MT
(
1
2
 ̈
t
2
2

ift•2(d+ 1)
2
.
Informally, by the collision lemma in Section 18.3, breaking the binding property implies a
collision in the query-answer traces of the two executions ofMT.Check. The proof below upper
bounds the probability that the adversary produces outputs that result in such a collision.
Note that a straightforward analysis would consider the probability of a collision in the
query-answer trace resulting from concatenating the adversary’s trace and the query-answer
traces of the two executions ofMT.Check; this would yield a bound of

t+2(d+1)
2

 ̈
1
2

. The proof
below improves on this upper bound via a more careful analysis of which collisions are relevant.
Proof.Lettrbe the query-answer trace ofA
f
. We define two events:
•Eis the event thatA’s output satisfies the conditions in the probability statement; and
•E
col
is the event thattrcontains a collision.
Our goal is to upper bound the probability thatEholds.
We break the analysis into two cases as follows:
Pr[E]=Pr[E^E
col
]+Pr[E^E
col
].
We upper bound each term individually, yielding the claimed upper bound.
1.The probability ofE^E
col
is upper bounded by the probability ofE
col
, which by
Lemma 3.3.1 is at most
1
2
 ̈
(t ́1) ̈t
2

.
2.The eventE^E
col
implies that
•trcontains no collisions,
•DiPI
0
XI
1
s.t.a
0
[i]‰a
1
[i],
•MT.Check
f
(rt,I
0
,a
0
,pf
0
)=1, and
•MT.Check
f
(rt,I
1
,a
1
,pf
1
)=1.
LetiPI
0
XI
1
be the minimal index such thata
0
[i]‰a
1
[i]. Letauth
0
andauth
1
be the
authentication paths for locationiinpf
0
andpf
1
respectively. Define the query-answer
traces:
•S
0
is the query-answer trace ofMT.Check
f
(rt,i,a
0
[i],auth
0
); and
•S
1
is the query-answer trace ofMT.Check
f
(rt,i,a
1
[i],auth
1
).

18 Merkle commitment scheme196
Note thatMT.Check
f
(rt,I
0
,a
0
,pf
0
)=1implies thatMT.Check
f
(rt,i,a
0
[i],auth
0
)=1, and
similarlyMT.Check
f
(rt,I
1
,a
1
,pf
1
)=1implies thatMT.Check
f
(rt,i,a
1
[i],auth
1
)=1.
By Lemma 18.3.2 we get a collision in these traces: there are distinct queriesx
0
,x
1
and an
answerysuch that(x
0
,y)PS
0
and(x
1
,y)PS
1
. Thus, we show that
Pr[E^E
col
]§Pr

trcontains no collisions and there exist
(x
0
,y)PS
0
and(x
1
,y)PS
1
withx
0
‰x
1

§
(d+ 1)
2
2

.
We are left to argue the second inequality above. Sincetrcontains no collisions, it cannot
be that(x
0
,y)Ptrand(x
1
,y)Ptrsimultaneously. Fix any pair of distinct queries(x
0
,x
1
)
such thatx
0
appears as a query inS
0
andx
1
appears as a query inS
1
, but not both
queries are intr. Then, the probability thatf(x
0
)=f(x
1
)is
1
2

. Taking a union bound
over all such pairs(x
0
,x
1
), the probability that there exist(x
0
,y)PS
0
and(x
1
,y)PS
1
withx
0
‰x
1
is at most
|
S
0
|
 ̈
|
S
1
|
2

. The claimed bound then follows since
|
S
0
|
,
|
S
1
|
§d+1
(MT.Checkmakes one query to compute the commitmentc
(d,i)
and thendqueries to
compute the commitments(c
p(i,j)
)
jPt0,1,...,d ́1u
).
We conclude that
Pr[E]=Pr[E^E
col
]+Pr[E^E
col
]
§
1
2
 ̈
(t ́1) ̈t
2

+
(d+ 1)
2
2

.
Finally, ift•2(d+ 1)
2
then the above expression is at most
1
2
 ̈
t
2
2

.
We additionally state a lemma that captures binding in the case where the commitment is
honestly generated byMT.Commiton a given message, and the adversary wins if the adversary
produces a valid opening that is inconsistent with the message. The lemma directly follows
from Lemma 18.4.1, and we use it in Chapter 32.
Lemma 18.4.2.LetMT
:
=MT[
:
=log
2
`. For every query boundtPN
andt-query algorithmA,
Pr
2
6
6
4
MT.Check
f
(rt,I,a,pf)=1
^m[I]‰a
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(m,aux)–A
f
(rt,td)–MT.Commit
f
(m)
(I,a,pf)–A
f
(aux,rt,td)
3
7
7
5
§✏
h
MT
(
Above,✏
h
MT
(
1
2
 ̈
(t+2 ̈`)
2
2

ift•2(d+ 1)
2
.
Proof.We reduce to the binding property ofMTin Lemma 18.4.1. LetA
2
be the algorithm
that, usingAas a subroutine, works as follows.
A
f
2
:
1.(m,aux)–A
f
.
2.(rt,td)–MT.Commit
f
(m).
3.(I,a,pf
0
)–A
f
(aux,rt,td).
4.pf
1
–MT.Open
f
(td,I).
5.Output(rt,I,a,pf
0
,I,m,pf
1
).

18 Merkle commitment scheme197
The algorithmA
2
makes at mostt
2
:
=t+2`queries. Moreover,MT.Check
f
(rt,I,m,pf
1
)=1
holds always for its output. Therefore,
Pr
2
6
6
4
MT.Check
f
(rt,I,a,pf)=1
^m[I]‰a
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(m,aux)–A
f
(rt,td)–MT.Commit
f
(m)
(I,a,pf)–A
f
(aux,rt,td)
3
7
7
5
=Pr
2
4
DiPIs.t.a[i]‰m[i]
^MT.Check
f
(rt,I,a,pf
0
)=1
^MT.Check
f
(rt,I,m,pf
1
)=1
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,I,a,pf
0
,I,m,pf
1
)–A
f
2
3
5
§
1
2
 ̈
t
2
2
2

(by Lemma 18.4.1)
=
1
2
 ̈
(t+2 ̈`)
2
2

.
18.5 Extractability
We prove that the Merkle commitment scheme isextractable, a security property that informally
states that if an adversary outputs a Merkle commitment and then subsequently opens the Merkle
commitment at a subset of locations then the adversary “knew” the opening at commitment
time. In Section 18.5.1 we study this property for one commitment, in Section 18.5.2 we study
it for multiple commitments, and in Section 18.5.3 we study it for multiple commitments across
multiple configurations.
18.5.1 Extraction for one commitment
The extractability property is formalized via an efficient algorithmMT.Extractknown as
theextractor. This is analogous to the extractability property that we proved for the basic
commitment schemeCMin Chapter 17 (see Section 17.2), but for a major difference. Namely,
we cannot expect to extract an entire message for a given Merkle commitment.
The adversary may output a Merkle commitment obtained from a partial tree, and then
subsequently open parts of this partial tree. HenceMT.Extract(an efficient algorithm) cannot
output an entire message whose Merkle commitment is the one output by the adversary, because
that would entail, e.g., inverting the random oracle.
In light of the above, the extractability property only requiresMT.Extractto output a message
that agrees with the adversary only at locations that the adversary knows how to open. In
particular, if the adversary never provides an opening for certain locations then no requirements
are imposed on those locations of the extracted message.
In more detail, we consider an experiment of the following form.
•First, in a commitment phase, the adversary, given oracle access to the random oracle,
performs a computation and outputs a Merkle commitmentrtand a private stateaux. Let
trbe the query-answer trace of the adversary in this phase.

18 Merkle commitment scheme198
•Then, in an opening phase, the adversary, given oracle access to the random oracle and as
input the private stateaux, continues its computation and outputs an index setI, opening
valuesa, and opening proofpf.
Extractability states that if the adversary’s output satisfiesMT.Check
f
(rt,I,a,pf)=1then the
extractorMT.Extract, given the Merkle commitmentrtand the query-answer tracetr, outputs
a messagemand opening trapdoortdsuch thatmagrees withaonIandtdleads to the
opening proofpfwhen specialized toI. (Up to a small error.) In other words, the adversary
“knew” the local opening in the commitment phase because the extractor found it by examining
only the query-answer trace of the adversary relevant for producing the commitment (without
seeing the subsequent query-answer trace in the opening phase).
The lemma below formally states the property and provides the extraction error.
Lemma 18.5.1(MTis extractable).LetMT
:
=MT[
:
=log
2
`.  There
exists a deterministic algorithmMT.Extractsuch that, for every query boundtPNandt-query
algorithmA,
Pr
2
6
6
6
6
6
4
MT.Check
f
(rt,I,a,pf)=1
^(m[I]‰a_pf
1
‰pf)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,aux)
tr
–›A
f
(m,td)–MT.Extract(rt,tr)
(I,a,pf)–A
f
(aux)
pf
1
–MT.Open
f
(td,I)
3
7
7
7
7
7
5
§
MT
(
Above:
•
MT
(
1
2
 ̈
(t ́1) ̈t
2

+
(d+1) ̈2`
2

(at most
1
2
 ̈
t
2
2

ift•4 ̈(d+ 1) ̈`);
•MT.Extractruns in timeet
MT
(

t ̈` ̈(log
|
⌃
|
+s+

.
We describe the intuition behind the extractorMT.Extract, and then provide a formal
description of it. The extractorMT.Extractis tasked with finding a message that “explains” any
future opening to a given Merkle commitmentrt, given the query-answer trace of the adversary
that produced the Merkle commitment. Intuitively, all the information about possible openings
of the adversary is available in the query-answer trace of the adversary’s computation till it
outputs the Merkle commitmentrt. So the extractor merely needs to organize the query-answer
trace into a partial tree, and read off the leaves of this tree, filling in with an arbitrary value
any missing leaves. Because a random oracle is inversion resistant and collision resistant, no
adversary is able to provide any other openings other than those contained in the leaves output
this way, up to a small probability of error.
In order to define the extractor, it will be convenient to partition the queries into three types:
leaf queries (for computing the leaves of the Merkle tree), inner vertex queries (for computing
the internal vertices of the tree), and other (queries that do not match these previous categories).
After that we describe the extractorMT.Extract.
Definition 18.5.2.Lettr=

(x
i
,y
i
)

iP[t]
be a query-answer trace for an oraclef:t0,1u
 ̊
Ñ
t0,1u

. We partition the query-answer pairs intraccording to threetypes of queries.
1.Leaf vertex queries.A settr
leaf
that contains queries-answer pairs(x, y)wherex=(m, ⌧)
for some message entrymP⌃and salt⌧Pt0,1u
s
.
2.Inner vertex queries.A settr
inner
that contains queries-answer pairs(x, y)wherexPt0,1u
2
.
3.Other queries.A settr
other
that contains all other query-answer pairs.

18 Merkle commitment scheme199
Construction 18.5.3.Given as input a Merkle commitmentrtPt0,1u

and query-answer
tracetr=

(x
i
,y
i
)

iP[t]
,MT.Extractworks as follows.
1.Ifrtis not the answer to any query intr, then output(m,td)
:
=(K,K).
2.Lettr
leaf
,tr
inner
,tr
other
be the partitioning oftraccording to Definition 18.5.2.
3.Label the binary treeT
`
(see Definition 18.1.1) as follows:
•The root ofT
`
is labeled withrt.
•While there is a query-answer pair(x, y)Ptr
inner
whereyis a label of a vertex inT
`
, set
the label of the left child to be[x]
L
and the label of the right child to be[x]
R
(where
[x]
L
and[x]
R
are the left half and right half ofx). Remove(x, y)fromtr
inner
.
•While there is a query-answer pair(x, y)Ptr
leaf
whereyis the label of thei-th leaf of
T
`
for someiP[`], setm
i
:
=mand⌧
i
:
=⌧, wherex=(m, ⌧). Remove(x, y)from
tr
leaf
.
4.Set arbitrarily the values of any label inT
`
or pair(m
i
,⌧
i
)not defined in the previous step.
5.Set the commitmentsC
:
=((c
(j,i)
)
iP[2
j
]
)
d
j=0
, wherec
(j,i)
is the label of thei-th vertex in
layerjof the treeT
`
.
6.Set the message vectorm
:
=(m
i
)
iP[`]
.
7.Set the opening trapdoortd
:
=(⌧,C), where⌧
:
=(⌧
i
)
iP[`]
.
8.Output(m,td).
Proof of Lemma 18.5.1.We discuss the time complexity ofMT.Extractin Remark 18.5.5. Below
we analyze its success probability.
Consider the following query-answer traces:
•tris the query-answer trace of the execution(rt,aux)
tr
–›A
f
;
•tr
1
is the query-answer trace of the execution(I,a,pf)
tr
1
–›A
f
(aux);
•Sis the query-answer trace of the executionMT.Check
f
(rt,I,a,pf).
Fix anyt
1
,t
2
PNwitht
1
+t
2
§t. We prove the claimed upper bound conditioned on the
event thatt
1
=
|
tr
|
andt
2
=
|
tr
1
|
. The lemma follows from this because the upper bound holds
for everyt
1
,t
2
PNwitht
1
+t
2
§t, and every computation of thet-query adversaryAimplies
a setting oft
1
,t
2
PNwitht
1
+t
2
§t.
We define several events:
•Eis the event that the conditions in the probability statement hold;
•E
col
is the event thattrcontains a collision;
•E
tree
is the event thatT
`
‰
ˆ
T
`
where
–T
`
is the tree generated in the execution ofMT.Extract(rt,tr)and
–
ˆ
T
`
is the tree generated in the execution ofMT.Extract(rt,tr}tr
1
).
•E
sub
is the event thatSÜtrandMT.Check
f
(rt,I,a,pf)=1.
Our goal is to upper bound the probability thatEholds. We break the analysis into four cases:
Pr[E]§Pr[E
col
]+Pr
⇥
E
tree
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
+Pr
⇥
E
ˇ
ˇ
E
col
^E
tree
^E
sub
⇤
.
We upper bound each term individually, yielding the claimed upper bound.

18 Merkle commitment scheme200
1.An upper bound on the probability of the eventE
col
follows directly from Lemma 3.3.1:
Pr[E
col
]§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

.
2.We upper bound the probability of the eventE
tree
ˇ
ˇ
E
col
.
IfT
`
‰
ˆ
T
`
then there exists a query intr
1
that is not intrwith an answer that equals a
non-dummy label inT
`
. (A non-dummy label is one added in Item 3 ofMT.Extract, rather
than Item 4.) We bound the probability that such a query exists.
Since the eventE
col
does not hold (trcontains no collisions), each vertex in the treeT
`
is labeled at most once. There are at mostmint2t
1
+1,2`unon-dummy labels inT
`
: the
root vertex is labeled separately, and each query intrresults in at most2newly-labeled
vertices; moreover, there are at most2`vertices in the treeT
`
. Hence the probability that
any fixed query intr
1
(that is not intr) has an answer that equals one of the labels inT
`
is
at most
mint2t
1
+1,2`u
2

.
Taking a union bound over all queries intr
1
,
Pr
⇥
E
tree
ˇ
ˇ
E
col
⇤
§
ˇ
ˇ
tr
1
ˇ
ˇ
 ̈
mint2t
1
+1,2`u
2

=t
2
 ̈
mint2t
1
+1,2`u
2

.
3.We upper bound the probability of the eventE
sub
ˇ
ˇ
E
col
^E
tree
.
For everyiPI, letS
i
ÑSbe the query-answer trace ofMT.Check
f
(rt,i,a[i],auth
i
), where
auth
i
is the authentication path for locationiinpf.
Suppose thatE
sub
holds. ThenSÜtr, so there existsiPIsuch thatS
i
Ütr. Moreover,
MT.Check
f
(rt,i,a[i],auth
i
)=1, so the query-answer traceS
i
can be viewed as a path that
“ends” in the Merkle commitmentrt, and thus “connects” somewhere intoT
`
(the tree
generated in the execution ofMT.Extract(rt,tr)). In sum, ifE
sub
holds then there exists
a query inS
i
that is not intrwith an answer that equals a non-dummy label inT
`
. (A
non-dummy label is one added in Item 3 ofMT.Extract, rather than Item 4.)
Since the eventE
col
does not hold (trcontains no collisions), each vertex in the treeT
`
is labeled at most once. There are at mostmint2t
1
+1,2`unon-dummy labels inT
`
(we
argued this in the prior point). Moreover,T
`
=
ˆ
T
`
becauseE
tree
does not hold. Hence
there are no queries intr
1
ztrthat have an answer that equals a non-dummy label inT
`
(otherwise, there would be a leaf in
ˆ
T
`
labeled differently from the corresponding leaf in
T
`
). Hence the probability that any fixed query inS
i
(that is not intrYtr
1
) has an answer
that equals a non-dummy label inT
`
is at most
mint2t
1
+1,2`u
2

.
Considering any choice ofIÑ[`]andiPIand taking a union bound over all queries inS
i
,
Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
§max
IÑ[`]
max
iPI
|S
i
| ̈
mint2t
1
+1,2`u
2

§(d+ 1) ̈
mint2t
1
+1,2`u
2

.
4.We show that the eventEcannot happen ifE
col
does not hold,E
tree
does not hold, and
E
sub
does not hold (in fact, it suffices to assumeE
col
^E
sub
but we includeE
tree
for
symmetry). We provide this as a claim (as we reuse it in later sections).

18 Merkle commitment scheme201
Claim 18.5.4.It holds that
Pr
2
6
6
6
6
6
4
MT.Check
f
(rt,I,a,pf)=1
^(m[I]‰a_pf
1
‰pf)
conditioned on
E
col
^E
tree
^E
sub
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,aux)
tr
–›A
f
(m,td)–MT.Extract(rt,tr)
(I,a,pf)–A
f
(aux)
pf
1
–MT.Open
f
(td,I)
3
7
7
7
7
7
5
=0.
Proof.The conditioning means that all of the eventsE
col
,E
tree
,E
sub
do not hold. Suppose
thatMT.Check
f
(rt,I,a,pf)=1(as otherwise the claim holds trivially). Then,SÑtr
(sinceE
sub
does not hold). Below we argue that (under the conditioning) this implies that
m[I]=aandpf
1
=pf. Note that the opening proofspfandpf
1
consist of authentication
paths(auth
i
)
iPI
and(auth
1
i
)
iPI
. Moreover, from Equation 18.3 we know that
MT.Check
f
(rt,I,a,pf)=
^
iPI
MT.Check
f
(rt,i,a[i],auth
i
),and
MT.Check
f
(rt,I,m[I],pf
1
)=
^
iPI
MT.Check
f
(rt,i,m[i],auth
1
i
).
•We show thatm[I]=a.
FixiPIand consider the following query-answer traces:
–S
i
is the query-answer trace of the executionMT.Check
f
(rt,i,a[i],auth
i
);
–S
1
i
is the query-answer trace of the executionMT.Check
f
(rt,i,m[i],auth
1
i
).
We know thatS
i
ÑS(sinceMT.Checkvalidates each authentication path in the
opening proof), soS
i
Ñtr. Moreover, we know thatMT.Check
f
(rt,i,a[i],auth
i
)=1
(sinceMT.Check
f
(rt,I,a,pf)=1).
Next, the extractorMT.Extract, given input(rt,tr), uses the query-answer pairs intr
to assign values to the entries ofmthat have a valid authentication paths intrto the
Merkle commitmentrt(see Item 3 of Construction 18.5.3); the remaining entries ofm
are assigned arbitrary values (see Item 4 of Construction 18.5.3). SinceS
i
Ñtr,we
know that thei-th entry ofmis assigned a non-arbitrary value (as the tracetrcontains
a path from thei-th leaf to the root), and henceS
1
i
Ñtr. Moreover, the opening
trapdoortdoutput byMT.ExtractenablesMT.Opento output valid authentication
paths for entries that are assigned non-arbitrary values, including the authentication
pathauth
1
i
, so we also deduce thatMT.Check
f
(rt,i,m[i],auth
1
i
)=1.
We have established that:
–S
i
is contained intr, andMT.Check
f
(rt,i,a[i],auth
i
)=1; and
–S
1
i
is contained intr, andMT.Check
f
(rt,i,m[i],auth
1
i
)=1.
Now suppose by way of contradiction thatm[I]‰a. By Lemma 18.3.2,trcontains a
collision, which contradicts the conditioning.
•We show thatpf
1
=pf.
Suppose by way of contradiction thatpf
1
‰pf. This means that there exists an index
iPIsuch thatauth
1
i
‰auth
i
. Above we argued thatm[I]=a, which means that
m[i]=a[i]. Above we also argued thatMT.Check
f
(rt,i,m[i],auth
1
i
)=1and that
MT.Check
f
(rt,i,a[i],auth
i
)=1, and that the corresponding tracesS
1
i
andS
i
are intr.
By Lemma 18.3.1,trcontains a collision, which contradicts the conditioning.

18 Merkle commitment scheme202
We conclude that
Pr[E]
§Pr[E
col
]+Pr
⇥
E
tree
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
+Pr
⇥
E
ˇ
ˇ
E
col
^E
tree
^E
sub
⇤
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
t
2
 ̈mint2t
1
+1,2`u
2

+
(d+ 1) ̈mint2t
1
+1,2`u
2

+0
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+d+ 1) ̈mint2t
1
+1,2`u
2

(sincet
1
+t
2
§t)
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+d+ 1) ̈2`
2

.(since minta, bu§a, b)
The expression is a convex function int
1
so its maximum on the intervalt
1
Pt0,1,...,tuis
achieved at eithert
1
=0ort
1
=t. Hence the expression is upper bounded from the maximum
of these two options:
Pr[E]§max
"
(t+d+ 1) ̈2`
2

,
1
2
 ̈
(t ́1) ̈t
2

+
(d+ 1) ̈2`
2

*
.
We conclude that ift•4`+1(a very mild condition) then the first term is no more than the
second term, in which case
Pr[E]§
1
2
 ̈
(t ́1) ̈t
2

+
(d+ 1) ̈2`
2

.
Remark 18.5.5(time complexity ofMT.Extract).We discuss how a straightforward realization
ofMT.Extractleads to the time complexity claimed in Lemma 18.5.1, and how in common
parameter regimes this time complexity can be improved.
The dominant contribution comes from Item 3, which we discuss below. Indeed, all other steps
(partitioning queries, giving arbitrary values to unlabeled vertices in the tree, and assembling
the extractor outputs) can be performed in time at mostO

(t+`) ̈(log
|
⌃
|
+s+

.
Item 3 requires structuring certain information from the query-trace into a partial binary tree.
This involves at mostmint2`, tu=O(`)iterations (each iteration corresponds to a vertex in
the tree and an entry in the trace), proceeding layer by layer from the root towards the leaves.
Each iteration involves searching the query-answer trace for an entry in which the answer equals
the label of the vertex. Each of theseO(`)searches takes at most timeO

t ̈(log
|
⌃
|
+s+

,
which leads to the time complexityO

t ̈` ̈(log
|
⌃
|
+s+

claimed in Lemma 18.5.1.
We can do better by using suitable data structures. Realizing Item 3 essentially requires a
static dictionarybecause we need to performmint2`, tulookups into a (static) list of at mostt
entries, with each entry consisting of at mostw
:
=O(log|⌃|+s+
is to sort the query-answer trace by answers, and then perform lookups via binary search. Sorting
the trace takes timeO(t ̈logt ̈w)and performing each of themint2`, tulookups takes time
O(logt ̈w); this leads to a total time complexity ofO((t+mint2`, tu) ̈logt ̈w)=O(t ̈logt ̈w).
The above expression improves on the time in Lemma 18.5.1 provided that logt=O(`).
Remark 18.5.6(extractability implies binding).The extractability property in Lemma 18.5.1
is a strong security guarantee: any bounded-query adversary that opens a commitment must

18 Merkle commitment scheme203
have “known” the opening at commitment time. In fact,extractability is stronger than binding:
we show that ifMTsatisfies extractability with error
MT
thenMTsatisfies binding with error
✏
MT
§2 ̈
MT
(a closely related error).
3
LetAbe at-query algorithm that opens a commitment in two ways with probability✏
MT
:
✏
MT
:
=Pr
2
4
DiPI
0
XI
1
s.t.a
0
[i]‰a
1
[i]
^MT.Check
f
(rt,I
0
,a
0
,pf
0
)=1
^MT.Check
f
(rt,I
1
,a
1
,pf
1
)=1
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,I
0
,a
0
,pf
0
,I
1
,a
1
,pf
1
)–A
f
3
5
.
LetA
e
be thet-query algorithm for the extraction game that is defined as follows.
•A
f
e
: RunA
f
to get(rt,I
0
,a
0
,pf
0
,I
1
,a
1
,pf
1
), setaux
:
=(I
0
,a
0
,pf
0
,I
1
,a
1
,pf
1
), and output
(rt,aux).
•A
f
e
(aux): Sample a random bitb(by using private randomness or via a fresh additional
query to the random oracle) and output the tuple(I
b
,a
b
,pf
b
)stored inaux.
Fix any candidate extractorMT.Extract. Fix any output(rt,I
0
,a
0
,pf
0
,I
1
,a
1
,pf
1
)ofAthat
breaks the binding property (i.e., satisfies the conditions in the probability statement above).
If we runMT.Extractonrt(the commitment output byA
e
in the first step) andtr(the query-
answer trace byA
e
in the first step) then we obtain an output(m,td)that, with probability
at least1/2, satisfiesm[I]‰a
b
_pf‰pf
b
, wherepf
:
=MT.Open
f
(td,I
b
). This is because the
inputs to the extractorMT.Extractare independent of the bitb(which is sampled byA
e
after
the inputs toMT.Extractare determined). Moreover, by the definition ofA
e
, we know that
MT.Check
f
(rt,I
b
,a
b
,pf
b
)=1regardless of the choice of bitb. We deduce that
1
2
 ̈✏
MT
§Pr
2
6
6
6
6
6
4
MT.Check
f
(rt,I
b
,a
b
,pf
b
)=1
^(m[I]‰a
b
_pf‰pf
b
)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(rt,aux)
tr
–›A
e
f
(m,td)–MT.Extract(rt,tr)
(I
b
,a
b
,pf
b
)–A
f
e
(aux)
pf–MT.Open
f
(td,I
b
)
3
7
7
7
7
7
5
.
We conclude that any extraction error
MT
that can be proved must satisfy the relation
1
2
 ̈✏
MT
§
MT
which gives us the desired bound on the binding error✏
MT
.
18.5.2 Extraction for multiple commitments
We discuss how extractability extends to adversaries that output multiple Merkle commitments.
Intuitively, this should follow directly from Lemma 18.5.1 via a union bound: if the adversary
outputsncommitments and subsequently an opening for one of the commitments, then the
probability that the opening is valid but the extractor did not succeed for the corresponding
commitment is at mostntimes the error in Lemma 18.5.1. This error can, however, be improved.
Each execution of the Merkle commitment extractor is applied to a (possibly) different Merkle
commitment, but with (possibly different prefixes of) thesamequery-answer tracetr. This
enables a tighter analysis.
The lemma below extends Lemma 18.5.1 to the case where an adversary outputsnMerkle
commitments and the extractor is tasked to extract for the commitment that the adversary
chooses to open (successfully). Similarly to Lemma 17.2.2 for the basic commitment scheme
CM, we let the extractorMT.MultiExtractbe a stateful algorithm.
3
This implication loses a factor of2, and we present it merely for didactic purposes. Indeed, forMTwe prove
almost the same errors in Lemma 18.4.1 (binding error) and Lemma 18.5.1 (extraction error).

18 Merkle commitment scheme204
Lemma 18.5.7(MTis multi-extractable).LetMT
:
=MT[
:
=log
2
`.
There exists a deterministicstatefulalgorithmMT.MultiExtractsuch that for every query
boundtPN,t-query algorithmA, and number of commitmentsnPN,
Pr
2
6
6
6
6
6
6
6
6
6
4
✓
MT.Check
f
(rt
i
,I,a,pf)=1
^(m
i
[I]‰a_pf
1
‰pf)
◆
_
0
@
Di
1
,i
2
P[n]:
rt
i
1
=rt
i
2
^(m
i
1
,td
i
1
)‰(m
i
2
,td
i
2
)
1
A
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
aux
0
:
=K
Fori=1,...,n:
‚(rt
i
,aux
i
)
tr
i
–›A
f
(aux
i ́1
)
‚(m
i
,td
i
)–MT.MultiExtract(rt
i
,tr
i
)
(iP[n],I,a,pf)–A
f
(aux
n
)
pf
1
–MT.Open
f
(td
i
,I)
3
7
7
7
7
7
7
7
7
7
5
§
m
MT
(
Above:
•
m
MT
(
3
2
 ̈
(t ́1) ̈t
2

+
(d+1) ̈2`
2

+
(n ́1) ̈t
2

(at most
3
2
 ̈
t
2
2

+
(n ́1) ̈t
2

ift•2 ̈(d+ 1) ̈`);
•the total running time ofMT.MultiExtractacross theninvocations is
et
m
MT
(

n ̈t ̈` ̈(log
|
⌃
|
+s+

.
Proof.The stateful extractorMT.MultiExtractis similar to the (stateless) extractorMT.Extract
in Construction 18.5.3. The extractorMT.MultiExtractinternally maintains the concatenation
of all query-answer traces received so far (after thei-th invocation it stores the tracetr
:
=
tr
1
} ̈ ̈ ̈}tr
i
), and uses this trace to construct the message and trapdoor corresponding to the
given commitment.
MT.MultiExtract(rt
i
,tr
i
):
1.Appendtr
i
to the query-answer tracetrstored in the internal state.
2.Compute and output(m
i
,td
i
)
:
=MT.Extract(rt
i
,tr).
By Lemma 18.5.1 each invocation ofMT.Extractruns in time at mostO

t ̈` ̈(log|⌃|+s+

,
because the stored query-answer trace contains at mosttentries. Theninvocations yield
the claimed total running time. The time complexity can be improved via a suitable use of
dynamic data structures in the internal state (and foregoingMT.Extractas a subroutine); see
Remark 18.5.8.
Now we analyze the extraction error. Consider the following query-answer traces:
•tr
:
=tr
1
} ̈ ̈ ̈}tr
n
;
•tr
1
is the query-answer trace of the execution(i, I,a,pf)–A
f
(aux
n
);
•Sis the query-answer trace of the executionMT.Check
f
(rt
i
,I,a,pf).
Fix anyt
1
,t
2
PNwitht
1
+t
2
§t. We prove the claimed upper bound conditioned on the
event thatt
1
=|tr|andt
2
=|tr
1
|. The lemma follows from this because the upper bound holds
for everyt
1
,t
2
PNwitht
1
+t
2
§t, and every computation of thet-query adversaryAimplies
a setting oft
1
,t
2
PNwitht
1
+t
2
§t.
We define several events.
•Eis the event that the conditions in the probability statement hold.
•E
col
is the event thattrcontains a collision.
•E
tree,1
is the event thatT
i
`
‰
ˆ
T
i
`
where

18 Merkle commitment scheme205
–T
i
`
is the tree generated during the execution ofMT.Extract(rt
i
,tr
1
} ̈ ̈ ̈}tr
i
), and
–
ˆ
T
i
`
is the tree generated during the execution ofMT.Extract(rt
i
,tr}tr
1
).
•E
tree,2
is the event that there existi
1
,i
2
P[n]withrt
i
1
=rt
i
2
andT
i
1
`
‰T
i
2
`
where
–T
i
1
`
is the tree generated during the execution ofMT.Extract(rt
i
1
,tr
1
} ̈ ̈ ̈}tr
i
1
), and
–T
i
2
`
is the tree generated during the execution ofMT.Extract(rt
i
2
,tr
1
} ̈ ̈ ̈}tr
i
2
).
•E
tree
is the eventE
tree,1
_E
tree,2
.
•E
sub
is the event thatSÜtrandMT.Check
f
(rt
i
,I,a,pf)=1.
The trees(T
i
`
)
iP[n]
defined inE
tree
are the trees generated during the execution ofMT.MultiExtract:
for everyiP[n],MT.MultiExtract(rt
i
,tr
i
)corresponds toMT.Extract(rt
i
,tr
1
} ̈ ̈ ̈}tr
i
).
Our goal is to upper bound the probability thatEholds. We break the analysis into several
cases:
Pr[E]§Pr[E
col
]+Pr
⇥
E
tree,1
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
tree,2
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
+Pr
⇥
E
ˇ
ˇ
E
col
^E
tree
^E
sub
⇤
.
We upper bound each term individually, yielding the claimed upper bound.
1.An upper bound on the probability of the eventE
col
follows directly from Lemma 3.3.1:
Pr[E
col
]§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

.
2.We upper bound the probability of the eventE
tree,1
ˇ
ˇ
E
col
.
SinceE
tree,1
holds (T
i
`
‰
ˆ
T
i
`
),tr
i+1
} ̈ ̈ ̈}tr
n
}tr
1
contains a query that is not intr
1
} ̈ ̈ ̈}tr
i
with an answer that equals a non-dummy label inT
i
`
.
Since the eventE
col
does not hold (trcontains no collisions), the aforementioned query
cannot be intr
i+1
} ̈ ̈ ̈}tr
n
because that would form a collision intr. Hence it suffices to
upper bound the probability that there exists a query intr
1
that is not intr
1
} ̈ ̈ ̈}tr
i
with
an answer that equals a non-dummy label inT
i
`
.
Since the eventE
col
does not hold (trcontains no collisions), each vertex in any of the trees
(T
i
`
)
iP[n]
is labeled at most once. The number of non-dummy labels inT
i
`
is upper bounded
bymint3t
1
,2`u. The upper bound3t
1
is since trees are constructed from a trace of length
at mostt
1
and each query adds at most three labels in one tree (most queries add two
labels but the first one in a tree adds three since the root is added as a label as well). The
upper bound2`is since a tree has at most2`labels. For every query intr
1
, the probability
that the query answer equals one of the these non-dummy labels is at most
mint3t
1
,2`u
2

.
Taking a union bound over all queries intr
1
,
Pr
⇥
E
tree,1
ˇ
ˇ
E
col
⇤
§
ˇ
ˇ
tr
1
ˇ
ˇ
 ̈
mint3t
1
,2`u
2

=t
2
 ̈
mint3t
1
,2`u
2

.
3.We upper bound the probability of the eventE
tree,2
ˇ
ˇ
E
col
.
Since the eventE
col
does not hold (trcontains no collisions), each vertex in any of the
trees(T
i
`
)
iP[n]
is labeled at most once.

18 Merkle commitment scheme206
For everyi
1
,i
2
P[n]withi
1
†i
2
andrt
i
1
=rt
i
2
, ifT
i
1
`
‰T
i
2
`
then there must be a query
intr
1
} ̈ ̈ ̈}tr
i
2
that is not intr
1
} ̈ ̈ ̈}tr
i
1
with an answer that equals a non-dummy label in
T
i
1
`
. Below we upper bound the probability that such a pair of indexesi
1
,i
2
P[n]exist.
Suppose that, forjP[t
1
], the adversary’sj-th query happens in iterationi
2
of the loop
(i.e., at the end of this iteration the adversary outputsrt
i
2
). The number of non-dummy
labels in the firsti
2
 ́1treesT
1
`
,...,T
i
2
 ́1
`
is bounded in two ways.
•Each query-answer pair leads to§2new labels in a single tree plus at mosti
2
 ́1
root labels. This is at most2(j ́1) +i
2
 ́1§2(j ́1) +n ́1non-dummy labels.
•Each tree has at most2`labels and there arei
2
 ́1§n ́1trees. This is at most
(n ́1) ̈2`non-dummy labels.
Therefore the number of non-dummy labels is at most
mint2(j ́1) +n ́1,(n ́1) ̈2`u.
Hence the probability that the answer of thej-th query matches any of the non-dummy
labels is at most
mint2(j ́1)+n ́1,(n ́1) ̈2`u
2

.
Summing over allt
1
queries intr,
Pr
⇥
E
tree,2
ˇ
ˇ
E
col
⇤
§
t
1
ÿ
j=1
mint2(j ́1) +n ́1,(n ́1) ̈2`u
2

§t
1
 ̈
mintt
1
+n ́2,(n ́1) ̈2`u
2

.
4.We upper bound the probability of the eventE
sub
ˇ
ˇ
E
col
^E
tree
.
For everyi
1
PI, we define the subsetS
i
1
ÑSbe the query-answer trace of the execution
MT.Check
f
(rt
i
,i
1
,a[i
1
],auth
i
1
), whereauth
i
1
is the authentication path for locationi
1
inpf.
Suppose thatE
sub
holds. ThenSÜtr, so there existsi
1
PIsuch thatS
i
1
Ütr. Moreover,
MT.Check
f
(rt,i,a[i],auth
i
)=1, so the query-answer traceS
i
1
can be viewed as a path
that “ends” in the Merkle commitmentrt
i
, and thus “connects” somewhere intoT
i
`
. In
sum, ifE
sub
holds then there exists a query inS
i
1
that is not intrwith an answer that
equals a non-dummy label inT
i
`
.
Since the eventE
col
does not hold (trcontains no collisions), each vertex in any of the
trees(T
i
`
)
iP[n]
is labeled at most once. The number of non-dummy labels inT
i
`
is upper
bounded bymint3t
1
,2`u. The upper bound3t
1
is since the trees are constructed from a
trace of length at mostt
1
and each query can add at most three labels in one tree (most
queries add two labels but the first one in a tree adds three since the root is added as a
label as well). The upper bound2`is since each tree has at most2`labels. For every
query inS
i
1
(that is not intr), the probability that the query answer equals one of the
these non-dummy labels is at most
mint3t
1
,2`u
2

.
SinceE
tree
(and thusE
tree,1
), there are no queries intr
1
with an answer that equals a
non-dummy label inT
i
`
. Recall thatS
i
1
has lengthd+1. Taking a union bound over all
queries inS
i
1
, the probability that there exists a query inS
i
1
(that is not intrYtr
1
) with
an answer that equals a non-dummy label inT
i
`
is at most(d+ 1) ̈
mint3t
1
,2`u
2

.
Hence
Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
§(d+ 1) ̈
mint3t
1
,2`u
2

.

18 Merkle commitment scheme207
5.We show that the eventE
ˇ
ˇ
E
col
^E
tree
^E
sub
cannot happen.
First we argue that for everyi
1
,i
2
P[n]withrt
i
1
=rt
i
2
it holds that(m
i
1
,td
i
1
)=(m
i
2
,td
i
2
).
This follows directly from the fact thatE
tree,2
implies thatT
i
1
`
=T
i
2
`
, so the extracted
message vectors and trapdoor information are the same, namely,(m
i
1
,td
i
1
)=(m
i
2
,td
i
2
).
Next we argue that ifMT.Check
f
(rt
i
,I,a,pf)=1thenm
i
[I]=aandpf
1
=pf. This follows
from applying Claim 18.5.4 for all commitments(rt
i
)
iP[n]
, as we now explain. Fix any
iP[n], and consider the trace up to the point where the adversary outputsrt
i
(i.e., the trace
tr
1
} ̈ ̈ ̈}tr
i
), and the trace of all queries performed after (i.e., the tracetr
i+1
} ̈ ̈ ̈}tr
n
}tr
1
).
Since we assumeE
col
^E
tree
^E
sub
, both conditions in the probability statement of
Claim 18.5.4 hold as well. This implies that ifMT.Check
f
(rt
i
,I,a,pf)=1thenm
i
[I]=a
andpf
1
=pfas required.
We conclude that
Pr[E]
§Pr[E
col
]+Pr
⇥
E
tree,1
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
tree,2
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
+Pr
⇥
E
ˇ
ˇ
E
col
^E
tree
^E
sub
⇤
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
t
2
 ̈mint3t
1
,2`u
2

+t
1
 ̈
mintt
1
+n ́2,(n ́1) ̈2`u
2

+(d+ 1) ̈
mint3t
1
,2`u
2

+0
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+d+ 1) ̈mint3t
1
,2`u
2

+t
1
 ̈
mintt
1
+n ́2,(n ́1) ̈2`u
2

(sincet
1
+t
2
§t)
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+d+ 1) ̈2`
2

+
t
1
 ̈(t
1
+n ́2)
2

(since minta, bu§a, b)
=
3
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+d+ 1) ̈2`
2

+
t
1
 ̈(n ́1)
2

.
The expression is a convex function int
1
so its maximum on the intervalt
1
Pt0,1,...,tuis
achieved at eithert
1
=0ort
1
=t. Hence the expression is upper bounded from the maximum
of these two options (where the second term is no smaller than the first):
Pr[E]§max
"
(t+d+ 1) ̈2`
2

,
3
2
 ̈
(t ́1) ̈t
2

+
(d+ 1) ̈2`
2

+
(n ́1) ̈t
2

*
§
3
2
 ̈
(t ́1) ̈t
2

+
(d+ 1) ̈2`
2

+
(n ́1) ̈t
2

,
where the second inequality holds under the mild condition that3t•4` ́2n+3.
Remark 18.5.8(time complexity ofMT.MultiExtract).A straightforward realization of proce-
dureMT.MultiExtractleads to the time complexity claimed in Lemma 18.5.7, becauseMT.Extract
is run at mostntimes.
Iflogt=O(n ̈`)(a natural regime) then we can do better by using suitable data structures.
The idea is similar to the improved realization ofMT.Extractdescribed in Remark 18.5.5. The
main difference is thatMT.MultiExtractreceives, with each invocation, an additional query-
answer trace. We use a dynamic dictionary (instead of a static dictionary), for which inserts
and searches take timelogt ̈w(when there aretentries each consisting ofwbits); these are the
same costs as for a static dictionary. The total number of inserts into the dictionary ist, and the
total number of searches isO(n ̈`). This leads to a time complexity that isO((t+n ̈`) ̈logt ̈w)
wherew
:
=log
|
⌃
|
+s+
logt=O(n ̈`).

18 Merkle commitment scheme208
Remark 18.5.9(multiple openings).Lemma 18.5.7 considers the case where the adversary
outputs one opening, which suffices for the purposes of this book. More generally, one can
consider the case where the adversary outputsoPNopenings. The proof of Lemma 18.5.7
can be extended to this case, establishing an upper bound
m
MT
(
probability:
Pr
2
6
6
6
6
6
6
6
6
6
4
0
@
D◆P[o]:
MT.Check
f
(rt
i
◆
,I
◆
,a
◆
,pf
◆
)=1
^(m
i
◆
[I
◆
]‰a
◆
_pf
1
◆
‰pf
◆
)
1
A
_
0
@
Di
1
,i
2
P[n]:
rt
i
1
=rt
i
2
^(m
i
1
,td
i
1
)‰(m
i
2
,td
i
2
)
1
A
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
aux
0
:
=K
Fori=1,...,n:
‚(rt
i
,aux
i
)
tr
i
–›A
f
(aux
i ́1
)
‚(m
i
,td
i
)–MT.MultiExtract(rt
i
,tr
i
)

(i
◆
P[n],I
◆
,a
◆
,pf
◆
)

◆P[o]
–A
f
(aux
n
)
For◆P[o]:pf
1
◆
–MT.Open
f
(td
i
◆
,I
◆
)
3
7
7
7
7
7
7
7
7
7
5
.
Specifically, one can show the upper bound

m
MT
(
3
2
 ̈
(t ́1) ̈t
2

+
o ̈(d+ 1) ̈2`
2

+
(n ́1) ̈t
2

.
The analysis is a straightforward extension of the proof of Lemma 18.5.7.
For every◆P[o], letS
◆
be the query-answer trace of the executionMT.Check
f
(rt
i
◆
,I
◆
,a
◆
,pf
◆
).
The eventEis defined to be the new condition in the probability statement above; the events
E
col
,E
tree,1
,E
tree,2
,E
tree
are defined as before; andE
sub
is extended to be the event that there
exists◆P[o]withS
◆
ÜtrandMT.Check
f
(rt
i
◆
,I
◆
,a
◆
,pf
◆
)=1. The probability thatEholds is
broken into the same cases as in the proof of Lemma 18.5.7, and all but one of the terms are
upper bounded in the same way.
The only difference is the upper bound for the eventE
sub
ˇ
ˇ
E
col
^E
tree
(due to the new
definition ofE
sub
). Via an additional union bound on theoopenings, one can show that
Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
§o ̈(d+ 1) ̈
mint3t
1
,2`u
2

.
This different upper bound leads to the bound for
m
MT
(
Pr[E]
§Pr[E
col
]+Pr
⇥
E
tree,1
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
tree,2
ˇ
ˇ
E
col
⇤
+Pr
⇥
E
sub
ˇ
ˇ
E
col
^E
tree
⇤
+Pr
⇥
E
ˇ
ˇ
E
col
^E
tree
^E
sub
⇤
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
t
2
 ̈mint3t
1
,2`u
2

+t
1
 ̈
mintt
1
+n ́2,(n ́1) ̈2`u
2

+o ̈(d+ 1) ̈
mint3t
1
,2`u
2

+0
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+o ̈(d+ 1)) ̈mint3t
1
,2`u
2

+t
1
 ̈
mintt
1
+n ́2,(n ́1) ̈2`u
2

(sincet
1
+t
2
§t)
§
1
2
 ̈
(t
1
 ́1) ̈t
1
2

+
(t ́t
1
+o ̈(d+ 1)) ̈2`
2

+
t
1
 ̈(t
1
+n ́2)
2

(since minta, bu§a, b)
§max
"
(t+o ̈(d+ 1)) ̈2`
2

,
3
2
 ̈
(t ́1) ̈t
2

+
o ̈(d+ 1) ̈2`
2

+
(n ́1) ̈t
2

*
(convexity int
1
)
§
3
2
 ̈
(t ́1) ̈t
2

+
o ̈(d+ 1) ̈2`
2

+
(n ́1) ̈t
2

(provided3t•4` ́2n+3).

18 Merkle commitment scheme209
18.5.3 Extraction for multiple configurations and commitments
We discuss how extractability further extends to adversaries that output multiple Merkle
commitments across multiple configurations. We consider a setting with multiple configurations
(MT
j
:
=MT[
j
,`
j
,s])
jP[k]
of the Merkle commitment scheme each using a corresponding
random oracle(f
j
)
jP[k]
PU
b
(
k
. The adversary outputs at mostncommitments for each of the
kconfigurations; and subsequently the adversary outputs a single opening per configuration.
The special casek=1corresponds to the setting in Lemma 18.5.7.
Lemma 18.5.10(MTis multi-extractable across configurations).Let(MT
j
:
=MT[
j
,`
j
,s])
jP[k]
and define(d
j
:
=log
2
`
j
)
jP[k]
. There exists a deterministicstatefulalgorithmMT
[k]
.MultiExtract
such that for every query boundtPN,t-query algorithmA, and number of commitments per
configurationnPN,
Pr
2
6
6
6
6
6
6
6
6
6
6
6
6
6
4
|
N
1
|
,...,
|
N
k
|
§n
and the following disjunction holds:
0
@
D◆P[k]:
MT
◆
.Check
f
◆
(rt
i
◆
,I
◆
,a
◆
,pf
◆
)=1
^(m
i
◆
[I
◆
]‰a
◆
_pf
1
◆
‰pf
◆
)
1
A
_
0
@
D◆P[k]Di
1
,i
2
PN
◆
:
rt
i
1
=rt
i
2
^(m
i
1
,td
i
1
)‰(m
i
2
,td
i
2
)
1
A
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f=(f
j
)
jP[k]
–U
b
(
k
aux
0
:
=K
N
1
,...,N
k
:
=H
Fori=1,2,...:
‚(j
i
P[k],rt
i
,aux
i
)
tr
i
–›A
f
(aux
i ́1
)
‚(m
i
,td
i
)–MT
[k]
.MultiExtract(j
i
,rt
i
,tr
i
)
‚additoN
j
i

(i
◆
PN
◆
,I
◆
,a
◆
,pf
◆
)

◆P[k]
–A
f
(aux
n
)
For◆P[k]:pf
1
◆
–MT
◆
.Open
f
◆
(td
i
◆
,I
◆
)
3
7
7
7
7
7
7
7
7
7
7
7
7
7
5
§
mm
MT
(
j
)
jP[k]
,t,n).
Above:
•
mm
MT
(
j
)
jP[k]
,t,n)§
3
2
 ̈
(t ́1) ̈t
2

+
(max
jP[k]
d
j
+1) ̈2
∞
jP[k]
`
j
2

+
(n ́1) ̈t
2

(at most
3
2
 ̈
t
2
2

+
(n ́1) ̈t
2

ift•2 ̈(max
jP[k]
d
j
+ 1) ̈
∞
jP[k]
`
j
);
•the total running time ofMT
[k]
.MultiExtractacross theninvocations is
et
mm
MT
(
j
)
jP[k]
,(`
j
)
jP[k]
,s,t,n)=O

n ̈t ̈max
jP[k]
`
j
 ̈(logmax
jP[k]
|⌃
j
|+s+

.
Proof.The stateful extractorMT
[k]
.MultiExtractis a straightforward generalization of the
stateful extractor in the proof Lemma 18.5.7. The extractorMT
[k]
.MultiExtractinternally
maintains the concatenation of all query-answer traces received so far (after thei-th invocation
it stores the tracetr
:
=tr
1
} ̈ ̈ ̈}tr
i
), and uses the relevant Merkle commitment extractor on
the appropriate subtrace to construct the message and trapdoor corresponding to the given
commitment.
MT
[k]
.MultiExtract(j
i
,rt
i
,tr
i
):
1.Appendtr
i
to the query-answer tracetrstored in the internal state.
2.Lettr
j
i
be the sub-trace corresponding to the oraclef
j
i
.
3.Compute and output(m
i
,td
i
)
:
=MT
j
i
.Extract(rt
i
,tr
j
i
).
By Lemma 18.5.1, for everyjP[k], each invocation ofMT
j
.Extractruns in time at most
O

t
j
 ̈`
j
 ̈(log
|
⌃
j
|
+s+

, wheret
j
is the number of queries byAto the oraclef
j
; note that

18 Merkle commitment scheme210
∞
jP[k]
t
j
§t.
4
Theninvocations, each for somejP[k], yield the claimed total running time:
n ̈max
jP[k]
O

t
j
 ̈`
j
 ̈(log|⌃
j
|+s+

=O

n ̈t ̈max
jP[k]
`
j
 ̈(logmax
jP[k]
|⌃
j
|+s+

.
Next, we discuss the extraction error. The analysis relies on Lemma 18.5.7 and the fact that
each Merkle commitment has its own random oracle.
For eachjP[k]lett
j
is the number of queries byAto the oraclef
j
, and letn
j
be a bound on
the number of commitments forMT
j
output byA. Further below we argue that the probability
in the lemma statement is at most
∞
jP[k]

m
MT
(
j
,t
j
,n
j
), where
m
MT
is the Merkle commitment
multi-extraction error from Lemma 18.5.7. This suffices to show the claimed bound because:
ÿ
jP[k]

m
MT
(
j
,t
j
,n
j
)
§
ÿ
jP[k]
3
2
 ̈
(t
j
 ́1) ̈t
j
2

+
(d
j
+ 1) ̈2`
j
2

+
(n
j
 ́1) ̈t
j
2

(by Lemma 18.5.7)
§
ÿ
jP[k]
3
2
 ̈
(t
j
 ́1) ̈t
j
2

+
(d
j
+ 1) ̈2`
j
2

+
(n ́1) ̈t
j
2

(since max
jP[k]
n
j
§n)
§
3
2
 ̈
(t ́1) ̈t
2

+
ÿ
jP[k]
2 ̈(d
j
+ 1) ̈`
j
2

+
n ̈t
2

(since
ÿ
jP[k]
t
j
§t)
§
3
2
 ̈
(t ́1) ̈t
2

+
(max
jP[k]
d
j
+ 1) ̈2
∞
jP[k]
`
j
2

+
(n ́1) ̈t
2

.
We are left to argue the upper bound in terms of
m
MT
.
For each◆P[k]letE
◆
denote the event that, in the experiment of the lemma statement,
|
N
◆
|
§n
◆
and either of the other two conditions holds for◆. The event in the lemma statement
implies that_
◆P[k]
E
◆
, so its probability is at mostPr[_
◆P[k]
E
◆
]§
∞
◆P[k]
Pr[E
◆
]. We now argue
that Pr[E
◆
]§
m
MT
(
◆
,t
◆
,n
◆
).
Consider the adversaryA
◆
that, given oraclef
◆
, emulatesAas follows.
A
f
◆
◆
:
1.Lazily samplek ́1oracles fromU
b
(
◆
into a vector of
oracles(f
j
)
jP[k]
distributed according toU
b
(
k
.
2.Start emulatingA
(f
j
)
jP[k]
.
3.WheneverAoutputs a tuple(j
i
,rt
i
,aux
i
)do: ifj
i
‰◆then do nothing; else ifj
i
=◆
then output(rt
i
,aux
i
).
4.WhenAhalts and outputs

(i
◆
,I
◆
,a
◆
,pf
◆
)

◆P[k]
, halt and output(i
◆
,I
◆
,a
◆
,pf
◆
).
The adversaryA
◆
makes at mostt
◆
queries to the oraclef
◆
and outputs at mostn
j
commitments.
Moreover, ifE
◆
holds forAthenA
◆
satisfies the conditions in the probability statement of
Lemma 18.5.7. We conclude that Pr[E
◆
]§
m
MT
(
◆
,t
◆
,n
◆
).
Remark 18.5.11(multiple openings per configuration).Lemma 18.5.10 considers the case
where the adversary outputs at mostncommitments per configuration and then one opening
4
Recall that the time complexity of eachMT
j
.Extractcan be improved via a suitable use of dynamic data structures
in the internal state (and foregoingMT
j
.Extractas a subroutine); see Remark 18.5.8.

18 Merkle commitment scheme211
per configuration, which suffices for the purposes of this book. More generally (and analogously
to Remark 18.5.9), one can consider the case where, for eachjP[k], the adversary outputs at
mostn
j
commitments ando
j
openings for configurationMT
j
. The proof of Lemma 18.5.10 can
be extended to this case, establishing an upper bound
mm
MT
(
j
)
jP[k]
,t,(n
j
)
jP[k]
,(o
j
)
jP[k]
)for
the following probability:
Pr
2
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
4
|
N
1
|
§n
1
,...,
|
N
k
|
§n
k
and the following disjunction holds:
0
@
DjP[k]D◆P[o
j
]:
MT
j
.Check
f
j
(rt
i
j,◆
,I
j,◆
,a
j,◆
,pf
j,◆
)=1
^(m
i
j,◆
[I
j,◆
]‰a
j,◆
_pf
1
j,◆
‰pf
j,◆
)
1
A
_
0
@
D◆P[k]Di
1
,i
2
PN
◆
:
rt
i
1
=rt
i
2
^(m
i
1
,td
i
1
)‰(m
i
2
,td
i
2
)
1
A
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f=(f
j
)
jP[k]
–U
b
(
k
aux
0
:
=K
N
1
,...,N
k
:
=H
Fori=1,2,...:
‚(j
i
P[k],rt
i
,aux
i
)
tr
i
–›A
f
(aux
i ́1
)
‚(m
i
,td
i
)–MT
[k]
.MultiExtract(j
i
,rt
i
,tr
i
)
‚additoN
j
i

(i
j,◆
PN
◆
,I
j,◆
,a
j,◆
,pf
j,◆
)

jP[k]
◆P[o
j
]
–A
f
(aux
n
)
ForjP[k],◆P[o
j
]:
‚pf
1
j,◆
–MT
j
.Open
f
j
(td
i
j,◆
,I
j,◆
)
3
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
5
.
An argument similar to the proof of Lemma 18.5.10 shows that if the adversaryAmakes at most
(t
j
)
jP[k]
queries to the oracles(f
j
)
jP[k]
respectively then
mm
MT
(
j
)
jP[k]
,t,(n
j
)
jP[k]
,(o
j
)
jP[k]
)§
∞
jP[k]

m
MT
(
j
,t
j
,n
j
,o
j
), where
m
MT
is the bound for multiple openings discussed in Re-
mark 18.5.9. The expression can then be simplified using the fact that
∞
jP[k]
t
j
§t.
18.6 Hiding
The binding and extractability properties of Merkle commitments protect the receiver from
malicious senders. Merkle commitments additionally satisfy certainhidingproperties, which
instead protect the sender. Informally, hiding ensures that information about the committed
message that the sender did not open is hidden from the receiver. The mechanism that enables
this is the random salts used to commit to each message entry at the leaf layer of the tree (see
Item 1 inMT.Commit); in fact, this mechanism can be viewed as using the basic commitment
schemeCM(from Chapter 17) to commit to each message entry.
We discuss hiding properties of Merkle commitments in two steps. In Section 18.6.1 we
explain how a Merkle commitment reveals no information about the committed message. Then
in Section 18.6.2 we explain how additionally providing an opening proof reveals no information
about the message beyond the opened entries of the message.
18.6.1 Merkle commitments hide the message
We prove that a Merkle commitmentrtreveals essentially no information about the underlying
committed messagem. Formally this is captured via the simulation paradigm: there exists
a polynomial-time probabilistic algorithmMT.SimulateRootthat samples a string, without
any information about the messagem, whose distribution is statistically close tort. This is
analogous to the hiding property for the basic commitment schemeCMin Chapter 17 (see
Lemma 17.3.1 in Section 17.3). Below we state the hiding property and prove the statistical
error bound. Note that the statistical error depends on several parameters: (a) the output size


18 Merkle commitment scheme212
of queriestto the random oracle made by an algorithm trying to distinguish between the two
distributions.
Lemma 18.6.1(rtis hiding).LetMT
:
=MT[
probabilistic algorithmMT.SimulateRootsuch that for every query boundtPNandt-query
algorithmA, the following two distributions are⇣
rt
MT
(
$
&
%
A
f
(aux,rt)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(mP⌃
`
,aux)–A
f
(rt,td)–MT.Commit
f
(m)
,
.
-
and
$
&
%
A
f
(aux,rt)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
(mP⌃
`
,aux)–A
f
rt–MT.SimulateRoot
f
,
.
-
.
Above,
⇣
rt
MT
(
CM
(
|
⌃
|
,s,t)+` ̈⇣
CM
(
where⇣
CM
is the hiding error ofCM=CM[
the bounds from the lemma we get that
⇣
rt
MT
(
#
` ̈t
2
s
+
` ̈t
2
2
ift†8
` ̈(2
 ́
s ́
2
+2
 ́
s
2
+2
 ́

2
)ift=8and
a
log
|
⌃
|
§`
.
Proof.The simulatorMT.SimulateRootoutputs a random string int0,1u

. The proof follows a
straightforward hybrid argument, in which we view each vertex in the Merkle tree as a basic
commitment.
Consider the leaf layer. Each leaf is a basic commitment as defined in Chapter 17. Using
Lemma 17.3.1, we can replace a leaf by a uniform random string overt0,1u

and lose an
additive term of⇣
CM
(
random strings gives us the error of` ̈⇣
CM
(
We continue layer by layer up to the root. Each vertex of the tree can be viewed as a basic
commitment where the left child is the empty message and the right child is a salt of size2
Replacing that vertex with a random string gives an error of⇣
CM
(
vertex, one by one, with a random string, until we reach the root. The number of vertices is at
most`, so overall this process yields an error of` ̈⇣
CM
(
Overall, the total error accumulated is at most` ̈⇣
CM
(
|
⌃
|
,s,t)+` ̈⇣
CM
(
Remark 18.6.2.In many cases, it is useful to have the simulator output a uniformly random
string, which is the case of our simulator. However, the second term in the error expression
fort=8can be avoided at the price of changing the simulator to output the root of a
Merkle commitment starting from random leaves instead of a uniformly random string. In
this case, we only need to replace the leaves with simulated ones and incur only an error of
` ̈⇣
CM
(
18.6.2 Merkle opening proofs hide the rest of the message
We prove that a Merkle opening proofpf, which is used to authenticate the entries of a message
in a subsetIÑ[`]of locations, hides the entries of the message outside ofI(i.e., with locations
in[`]zI). Formally, this is captured via the simulation paradigm: there exists a polynomial-time
probabilistic algorithmMT.Simulatethat, given as input the entries of the message inI, samples
a string whose distribution is statistically close topf. For convenience to later sections, the
property that we consider below additionally includes the Merkle commitmentrtin order to

18 Merkle commitment scheme213
provide ajointhiding property acrossrtandpf. In particular, the property below implies the
one above (Lemma 18.6.1) by takingI=H(as in this case the Merkle opening proof is empty
and the simulator receives no entries of the message).
Lemma 18.6.3(rtandpfare hiding).LetMT
:
=MT[
probabilistic algorithmMT.Simulatesuch that for every opening sizeqP[`], query boundtPN,
andt-query algorithmA, the following two distributions are⇣
MT
(
distance:
$
’
’
’
&
’
’
’
%
A
f
(aux,rt,pf)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
⇣
mP⌃
`
,IP

[`]
q

,aux
⌘
–A
f
(rt,td)–MT.Commit
f
(m)
pf–MT.Open
f
(td,I)
,
/
/
/
.
/
/
/
-
and
$
’
&
’
%
A
f
(aux,rt,pf)
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
ˇ
f–U
b
(
⇣
mP⌃
`
,IP

[`]
q

,aux
⌘
–A
f
(rt,pf)–MT.Simulate
f
(I,m[I])
,
/
.
/
-
.
Letting⇣
rt
MT
be the error defined and upper bounded in Lemma 18.6.1, we define the error function
⇣
MT
used above as follows:
•ifq=0then⇣
MT
(
:
=⇣
rt
MT
(
•ifq°0then⇣
MT
(
:
=max
IP(
[`]
q
)
∞
(j,i)PV
‹
(T
`
,I)
⇣
rt
MT
(
d ́j
,s,t), whereV
‹
(T
`
,I)
is the set of vertices in the copaths but not the paths forI, i.e.,
V
‹
(T
`
,I)
:
=copath(I)zpath(I)=(
Y
iPI
copath(i))z(
Y
iPI
path(i)).
In particular, ifq°0then taking⇣
MT
(
:
=q ̈
∞
jP[d]
⇣
rt
MT
(
d ́j
,s,t)suffices
because every copath contains one vertex per layer (except the root layer):
ÿ
(j,i)Pcopath(I)zpath(I)
⇣
rt
MT
(
d ́j
,s,t)§
ÿ
(j,i)Pcopath(I)
⇣
rt
MT
(
d ́j
,s,t)
§
ÿ
iPI
ÿ
jP[d]
⇣
rt
MT
(
d ́j
,s,t)
=q ̈
ÿ
jP[d]
⇣
rt
MT
(
d ́j
,s,t);
by Remark 18.6.9 ift†8this expression is at most
q ̈` ̈t
2
s
+
q ̈` ̈t
2
2
.
Note that ifq=0then the adversary receives only a Merkle commitmentrt; the adver-
sary receives no message entries or opening proofpf(it is empty). This degenerate case
corresponds to the setting of Lemma 18.6.1, so the statistical distance is upper bounded by
⇣
rt
MT
(
rt
MT
(
d
,s,t). Henceforth we assume thatq°0, which is the “interesting”
case of Lemma 18.6.3.
First we study the case of simulating (the Merkle commitment and) the opening proof for a
single leaf and then study the case of multiple leaves.

18 Merkle commitment scheme214
Single leafIn the case of a single leaf, the simulator receives a leaf indexiP[`]and a
message entryaP⌃, and is tasked to sample a Merkle commitmentrtand authentication
pathauthwhose distribution is close to that obtained by honestly committing to any message
whosei-th entry isaand then opening that location. Informally, the simulator does this by
sampling the salt for the leaf at random (just likeMT.Commitdoes), sampling the commitments
alongcopath(i)viaMT.SimulateRoot(rather than obtaining them from a computation on a
message), and computing from these the implied Merkle commitmentrtaccording to the way
an authentication path is checked. In more detail, the simulator is constructed as follows.
Construction 18.6.4.The simulator for the case of a single leaf works as follows.
MT.Simulate
f
(i,a):
1.Sample a random salt⌧
i
Pt0,1u
s
.
2.Compute the commitmentc
(d,i)
:
=f(a,⌧
i
).
3.Forj=d ́1,...,1,0:
a)Sample the commitmentc
 ̄
p(i,j+1)
–MT.SimulateRoot
f
.
b)Ifp(i, j+ 1)is an odd vertex then setc
L
:
=c
p(i,j+1)
andc
R
:
=c
 ̄
p(i,j+1)
.
c)Ifp(i, j+ 1)is an even vertex then setc
L
:
=c
 ̄
p(i,j+1)
andc
R
:
=c
p(i,j+1)
.
d)Compute the commitmentc
p(i,j)
:
=f(c
L
,c
R
).
4.Setrt
:
=c
(0,1)
.
5.Setauth
:
=

⌧
i
,(c
 ̄
p(i,j)
)
jPt1,...,du

. (For conveniencejnow ranges from1tod.)
6.Output(rt,auth).
The output of this simulator always validates, i.e., it is such thatMT.Check
f
(rt,i,a,auth)=1.
The number of queries to the random oracle isd+1. Intuitively, the statistical distance from
the real distribution is at most
∞
jP[d]
⇣
rt
MT
(
d ́j
,s,t)because of the following reasons.
•The salt⌧
i
inauthis distributed as in the real distribution.
•For everyjP[d], the commitmentc
 ̄
p(i,j)
inauthcan be viewed as a root of a subtree
of size2
d ́j
, and simulating it viaMT.SimulateRoot
f
contributes a statistical error of
⇣
rt
MT
(
d ́j
,s,t).
•The Merkle commitmentrtis determined by the other values and the random oracle.
Multiple leavesThe case of simulating a Merkle commitment and opening proof for multiple
leavesImay superficially look rather straightforward: for each leaf indexiPI, sample an
authentication path foriby following the simulator for a single leaf in Construction 18.6.4.
While intuitive, the above strategy doesnotwork. The problem is that the commitments
across multiple authentication paths inpfmay not be consistent with one another. First, the
same vertex may appear in multiple copaths, and thus its commitment is sampled multiple times
inconsistently; this problem is straightforwardly addressed by not sampling the commitment for
a vertex if it was already sampled.
5
Second, and this is more subtle, a commitment sampled as
part of the copath for a leaf index may be the result of an oracle query to check the copath of
another leaf index.
6
These considerations imply that the simulator should produce the opening
5
For example, for a message of size`=4, bothcopath(1)andcopath(2)contain the vertex(1,2).
6
For example, for a message of size`=4,copath(1)contains the vertex(1,2), and if the opening proof contains
authentication paths for entries1and3, then the commitment of the vertex(1,2)must be the output of the
random oracle applied to the commitment of vertices(2,3)(derived from entry3of the message and its salt)
and of(2,4)(provided incopath(3)).

18 Merkle commitment scheme215
proofpfin a more global way: sample all the commitments inpfthat do not depend on other
commitments, and then derive from these any remaining commitments inpfusing the random
oracle.
In more detail, an opening proofpffor an index setIcontains commitments for vertices in
copath(I)(vertices that belong to the copath corresponding to some location inI). For every
iPI, checking the authentication path corresponding toiinvolves computing the commitments
for vertices inpath(i)from the commitments for vertices incopath(i)(and the message entry
and salt). Hence, the commitments inpfthat are derived from other commitments are those in
path(I). We conclude that the commitments inpfthat are to be sampled are those corresponding
to vertices incopath(I)zpath(I). These considerations lead to the following simulator.
Construction 18.6.5.Given query access to a random oraclefPU
b
(
MT.Simulatereceives as input a subsetIand corresponding entries(m
i
)
iPI
of a message, and
works as follows.
MT.Simulate
f
(I,(m
i
)
iPI
):
1.IfI=H, setrt–MT.SimulateRoot
f
andpf
:
=K, and output(rt,pf).
2.For everyiPI, sample a random salt⌧
i
Pt0,1u
s
.
3.For everyiPI, compute the commitmentc
(d,i)
:
=f(m
i
,⌧
i
).
4.For every(j, i)Pcopath(I)zpath(I), setc
(j,i)
–MT.SimulateRoot
f
.
5.Forj=d, . . . ,1(in this order) andiP[2
j
]:
if(j, i)Ppath(I)then setc
(j,i)
:
=f(c
(j+1,2i ́1)
,c
(j+1,2i)
)Pt0,1u

.
6.Setrt
:
=c
(0,1)
. (Note that(0,1)Ppath(I).)
7.For everyiPI, setauth
i
:
=

⌧
i
,(c
v
)
vPcopath(i)

=

⌧
i
,(c
 ̄
p(i,j)
)
jPt1,...,du

.
8.Output(rt,pf)wherepf
:
=(auth
i
)
iPI
.
Definition 18.6.6.Two verticesv
1
,v
2
in the treeT
`
areindependentif the subtree rooted at
v
1
is disjoint from the subtree rooted atv
2
.
Claim 18.6.7.The vertices incopath(I)zpath(I)are pairwise independent.
Proof.Suppose there existv
1
andv
2
incopath(I)zpath(I)that are not independent. SinceT
`
is a tree, one must be a descendant of the other; without loss of generality,v
2
is a descendant
ofv
1
. Sincev
2
Pcopath(I), there existsiPIsuch thatv
2
Pcopath(i), and hence the siblingv
1
2
ofv
2
is inpath(i). The vertexv
1
2
is also a descendant ofv
1
. This tells us thatv
1
Ppath(i),a
contradiction.
Claim 18.6.8.For every(j, i)Ppath(I),(j+1,2i ́1),(j+1,2i)Pcopath(I)Ypath(I).
Proof.If(j, i)is on some path from a leaf vertex to the root vertex, one of the two children
(j+1,2i ́1)and(j+1,2i)of(j, i)is on that path and the other is on the corresponding
copath.
Proof of Lemma 18.6.3.FixmP⌃
`
andIP

[`]
q

. We argue that if the adversaryAoutputs
the message vectormand index setIthen the statistical distance between the two distributions
(conditioned on this output) is at most
∞
(j,i)PV
‹
(T
`
,I)
⇣
rt
MT
(
d ́j
,s,t)whereV
‹
(T
`
,I)=
copath(I)zpath(I). The lemma then follows by taking the maximum across all possible outputs
mandI.

18 Merkle commitment scheme216
The simulatorMT.Simulateproceeds layer by layer from the leaf vertices towards the root
vertex, setting the values of commitments in the opening proofpfeither by sampling them via
MT.SimulateRootor by deriving them via the random oracleffrom other commitments.
First we discuss the leaf layer. For everyiPI, the simulator samples a random salt
⌧
i
Pt0,1u
s
and sets the commitmentc
(d,i)
:
=f(m
i
,⌧
i
). This is distributed exactly as in the
real commitment experiment, so no simulation errors are incurred in the leaf layer.
Next we discuss the commitments((c
v
)
vPcopath(i)
)
iPI
=((c
 ̄
p(i,j)
)
jPt1,...,du
)
iPI
.
•By Claim 18.6.7, vertices incopath(I)zpath(I)are pairwise independent. Hence, for
every(j, i)Pcopath(I)zpath(I), settingc
(j,i)
–MT.SimulateRoot
f
incurs a simulation
error of⇣
rt
MT
(
d ́j
,s,t). Indeed,(j, i)is the root vertex of a perfect binary tree
of depthd ́j, and this perfect binary tree is disjoint from the perfect binary trees
of any other vertex incopath(I)zpath(I). Hence, the total simulation error here is
∞
(j,i)PV
‹
(T
`
,I)
⇣
rt
MT
(
d ́j
,s,t).
•By Claim 18.6.8, for every(j, i)Ppath(I),(j+1,2i ́1),(j+1,2i)Pcopath(I)Ypath(I).
Hence, the value of the commitmentc
(j,i)
is determined by the values of the commitments
c
(j+1,2i ́1)
andc
(j+1,2i)
, which the simulator has either previously sampled or computed.
Specifically, for correctness of the simulator’s output, the value of the commitmentc
(j,i)
must equal the answerf(c
(j+1,2i ́1)
,c
(j+1,2i)
). No simulation errors are incurred by setting
values for these commitments.
Finally, for correctness of the simulator’s output, the root commitmentrt
:
=c
(0,1)
must equal
the answerf(c
(1,1)
,c
(1,2)
). The values for both commitments are set by the simulator because
(0,1)Ppath(I). No simulation error is incurred by setting the root commitment.
Remark 18.6.9(expressions for⇣
MT
).The expressions for⇣
MT
in Lemma 18.6.3 are in terms
of⇣
rt
MT
. Here we describe the expression that we obtain for⇣
MT
in the caset†8when we plug
in the expression for⇣
rt
MT
in Lemma 18.6.1 (fort†8).
First we discuss the case of a single leaf. We get the expression⇣
MT
(
∞
jP[d]
⇣
rt
MT
(
d ́j
,s,t)§(
t
2
s
+
t
2
2
) ̈
∞
jP[d]
2
d ́j
=(
t
2
s
+
t
2
2
) ̈(2
d
 ́1)§
` ̈t
2
s
+
` ̈t
2
2
.
Next we discuss the case of multiple leaves, using the simplified upper bound at the end of
Lemma 18.6.3. We get the expressionq ̈
∞
jP[d]
⇣
rt
MT
(
d ́j
,s,t)§q ̈(
t
2
s
+
t
2
2
) ̈
∞
jP[d]
2
d ́j
=
q ̈(
t
2
s
+
t
2
2
) ̈(2
d
 ́1)§
q ̈` ̈t
2
s
+
q ̈` ̈t
2
2
.
Remark 18.6.10(superadditive and monotonic⇣
MT
).For convenience we assume that the
error bound⇣
MT
(
means that
⇣
MT
(
1
,s,q
1
,t)+⇣
MT
(
2
,s,q
2
,t)§⇣
MT
(
1
+`
2
,s,q
1
+q
2
,t).
In particular,⇣
MT
ismonotonic(more precisely, nondecreasing) in the message length and
opening size. This holds for the upper bound⇣
MT
(
∞
jP[d]
⇣
rt
MT
(
d ́j
,s,t)
in Lemma 18.6.3.
We use this to simplify certain expressions later on (in Sections 22.2 and 26.2). However,
tighter upper bounds on⇣
MT
might not be monotonic (and thus also not superadditive) in the
message length`or opening sizeq. If so one can consider the non-simplified expressions in our
analyses.
