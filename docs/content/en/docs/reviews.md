---
title: Reviews
date: 2025-09-01
weight: 3
---


This page documents the security reviews of Longfellow that have been completed by external organizations.

## Trail of Bits
Trail of Bits has reviewed our system and produced a 
[report](../../reviews/Longfellow_report_2025_08_18.pdf). All of the issues have been addressed in the latest release.  To briefly comment on the issues marked "High" severity:

1. Issue #1: The report noted that our library does not read each circuit to verify its hash.  Because our library is intended to be used in a high-performance server, our library provides these methods, but does not perform the check in *each* call to the verifier method. Instead, we expect a proper verifier implementation to perform this costly check once upon start and then cache the circuits in memory.  Our reference verifier implementation illustrates how this can be done.

10. Issue #10: Indeed, this report identified one under-constrained check in a circuit.  The check used a private (witness) variable to determine the length of a string, when instead, it should have used the public (available to the verifier) version of that length.  This issue has been resolved in the mdoc circuit.

## ISRG

1. ISRG-01. David Cook of ISRG reported a security flaw in our MDOC circuit that was patched on October 17th.  The error stems from under-constraining variables in the ZK circuit. Specifically, the hash circuit witness values representing indices into the CBOR data are missing checks that they are less than the length of the mdoc MSO, which is used in signature verification. Witness variables for bytes of the MSO past the "correct" SHA-256 block are effectively unconstrained, so if the CBOR index witness variables point into that region, then the prover can substitute its own values for mdoc fields.
    * To resolve this issue, additional checks have been added to verify that all bytes past the "correct" SHA-256 block are zero. Furthermore, all indices into the MDOC bytes are checked to be less than the number of bytes that are hashed. The number of bytes that are hashed is derived from the SHA block itself.
    * The change is available in [version 0.8.4](https://github.com/longfellow-zk/longfellow-zk/releases/tag/v0.8.4)

## Ligero Security Analysis
A group of 4 academic experts in the area of zero-knowledge, interactive oracle protocols (IOPs), and coding theory were assembled by Ligero to evaluate the Longfellow ZK protocol. In the course of their analysis, they independently produced two main security theorems that establish more precise concrete security guarantees of Longfellow. Here is their [full report](../../reviews/Longfellow_security_2025_12_15.pdf).

