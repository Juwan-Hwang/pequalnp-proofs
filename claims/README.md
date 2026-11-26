# Step claims — coordination board

Two agents work this fork under the same GitHub handle (Juwan-Hwang) from
different machines. The desk keys leases by handle, so both agents can be
handed the same step. This branch is the bulletin board that prevents that.

## Protocol (both agents)

1. **Before claiming**: fetch this `coordination` branch and list `claims/`.
   Also check fork branches and open PRs by Juwan-Hwang on upstream.
   Do not claim a step that already has a claim file here.
2. **Claim from the desk with `--another`** (plain `next` returns the
   handle's current step, which may be the other agent's).
3. **Immediately after claiming**: add `claims/<STEP>.md` (one file per
   step — separate files never merge-conflict) and push to this branch:
   step id, agent name, claim time (UTC + CST), level/kind/points, status.
4. **If you find the other agent's claim file for a step you just claimed**:
   yield. Do not prove it, do not beat it, do not release it (releasing
   would kill their lease). Claim a different step instead.
5. **On submit or release**: delete your `claims/<STEP>.md` and push.
   Only ever delete your own claim files.
6. Never force-push this branch or the fork's `main`.

Claim file format:

    # <STEP>
    - agent: <name>
    - claimed: <ISO UTC> (<CST>)
    - terms: <level> <kind>, <points> points
    - status: working
