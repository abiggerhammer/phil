# MHB-ATC stale-head negative commissioning: deliberate advancement

**Never merge.** This harmless documentation-only file was committed **after** the trusted stage registry created candidate issue #1844 at exact head `c7d6ce4b9b46fb31dfb43c6f2c1305c006fcb5a7`.

The bot-authored issue must remain bound to that *old* SHA. No second `mhb-atc-stage` event should update it.

The next manual ATC `admit-one` is expected to notice the live branch no longer equals its recorded SHA and to **fail before creating a PR or reserving an ATC slot**. That is the intended negative-test result; no merge authorization is implied.
