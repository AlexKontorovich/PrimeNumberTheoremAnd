# PrimeNumberTheoremAnd

This project has a blueprint, which is available at <https://AlexKontorovich.github.io/PrimeNumberTheoremAnd/web/>.
It requires [plasTeX](https://plastex.github.io/plastex/) and can be built using `make blueprint`.

# Use of LaTeX inside Lean

For those using github's copilot (free for educators), it's very convenient to have the natural language statements
right next to the Lean to be formalized. So we write the blueprint TeX right in the *.lean document, separated by
delimiters `/-%% text here %%-/` for multi-line and `--%% text here` for single-line TeX. The code automatically
scrapes these and populates the blueprint accordingly.
