"""The input's budget: what a spend can cost."""


def budget_ok(cost: int, program_bytes: int, witness_bytes: int) -> bool:
    """The input's budget, 1000 mWU per byte of its witness stack plus 50, covers the cost.  The stack is
    counted low: the program, the witness, the control block (33 bytes) and 9 bytes of length prefixes,
    without the CMR's 32 bytes."""
    return cost <= 1000 * (program_bytes + witness_bytes + 33 + 9 + 50)
