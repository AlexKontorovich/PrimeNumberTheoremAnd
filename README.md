# PrimeNumberTheoremAnd

This project has a blueprint, which is available at <https://AlexKontorovich.github.io/PrimeNumberTheoremAnd/web/>.

To use the tool, irst install local requirements using
```sh
python -pip install -r blueprint/requirements.txt
```

Then compile documentations using `make doc` in the top-level directory. Alternatively, if the PDF is needed, type
```sh
cd blueprint
make pdf
```

# Use of LaTeX inside Lean

For those using github's copilot (free for educators), it's very convenient to have the natural language statements
right next to the Lean to be formalized. So we write the blueprint TeX right in the *.lean document, separated by
delimiters `/-%% text here %%-/` for multi-line and `--%% text here` for single-line TeX. The code automatically
scrapes these and populates the blueprint accordingly.
