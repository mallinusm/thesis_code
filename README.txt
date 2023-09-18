Program verification with Separation logic
==========================================

This repo contains the Coq theories I created for the Master's thesis in CS at
the Vrije Universiteit Brussel (VUB), academic year 2022 - 2023. The idea with
this development is to mechanically verify software by generating, in an
operational Separation logic, verification conditions (VCs) shaped according to
the correctness properties of programs, and subsequently solve them
interactively in the Coq proof assistant. The implementation is proven sound,
i.e. realistic with respect to the semantics of the program language, in the
same system. The original plan was to develop symbolic execution such as to
apply various optimisations, this however turned out to be too optimistic to
complete in time. Instead, the tool generates VCs in a shallow universe of
propositions, though contracts can be specified in a deep universe.

Promoter: prof. dr. Steven Keuchel
