# Security Policy

## Supported versions

Phil is under active pre-release development. Until stable releases exist, security fixes are made against the current default branch. Older commits and experimental branches are not separately supported.

When Phil begins publishing supported releases, this section will be updated with explicit version ranges.

## What counts as a security issue?

Please report an issue privately if it could cause Phil to make, certify, or enforce a security-relevant claim that is not actually true.

Examples include:

* accepting a program, proof, certificate, or artifact that should have been rejected;
* unsoundness in a verifier, type system, proof boundary, or certification mechanism;
* compiler or backend behavior that violates a property Phil claims to preserve;
* discrepancies between checked and generated behavior that could cross a security boundary;
* unsafe handling of malformed or adversarial input;
* vulnerabilities that allow code execution, privilege escalation, information disclosure, or denial of service;
* compromise of the build, release, dependency, or certificate supply chain.

Ordinary bugs, documentation mistakes, feature requests, and theoretical disagreements can normally be reported through the public issue tracker. If you are unsure whether something has security implications, report it privately.

## Reporting a vulnerability

Please use GitHub's **private vulnerability reporting** for this repository rather than opening a public issue.

Include whatever information you have. A particularly useful report contains:

* the affected component or revision;
* what you expected to happen;
* what actually happened;
* a minimal reproducer, if available;
* why you believe the issue crosses a security or assurance boundary; and
* any known practical consequences.

A complete exploit is not required. A convincing demonstration that a claimed property does not hold is enough to warrant investigation.

## What to expect

Reports will be evaluated on their technical merits. We may ask for additional information or help reproducing the problem.

There is no guaranteed response-time SLA, but security reports will be treated as a priority. If a report is accepted, we will try to coordinate the fix and disclosure with the reporter.

Please give us a reasonable opportunity to investigate and correct a vulnerability before publishing details that would put users at risk. We will not ask reporters to keep vulnerabilities secret indefinitely.

Where appropriate, we will publish a GitHub security advisory describing the affected versions, impact, and fix, and will credit reporters who wish to be credited.

## Good-faith research

Good-faith investigation of Phil's security and assurance properties is welcome. Finding a way in which Phil is wrong about what it guarantees is a contribution to the project.
