# MeowThink

> 猫咪思考.jpg

MeowThink is a miniature dependent typed language intended to create a proof assistant within 2000 LOC of Rust.

It uses:
- A special equality type (to avoid the need to implement dependent pattern matching)
- Recursion with (restrictive) totality check
- Inductive type / type families
- Record types and modules

For examples, see files within the `testcases` directory. `tools` contains a VSCode extension providing basic syntax highlighting.

Currently MeowThink is in a WIP state. A lot of FIXMEs and TODOs are still in the source code!

## TODO
- [ ] Dependent ap
- [ ] Macros
- [ ] Axioms

## License
All source code within this repository is released under the MIT license. A full copy of the license text can be found in the LICENSE file.
