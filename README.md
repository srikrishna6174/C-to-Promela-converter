- input c code in input.C

//Running with GUI part(If there is any difficulty with this, you may proceed without it as mentioned below.)
   - pip install pycparser
* terminal 1:
   - direct to  code-view-converter-ui/src/codes
   - run "g++ code1.cpp -o code1 && ./code1 && python3 code2.py input.c -o output2.pml"
* terminal 2: 
   - direct to code-view-converter-ui directory
   - run "npm install" (only first time)
   - run "npm run dev"


//Running without GUI part
   - pip install pycparser
   - direct to code-view-converter-ui directory
   - run "g++ code1.cpp -o code1 && ./code1 && python3 code2.py input.c -o output2.pml"
   - you cn view outputs in the output1.pml and output2.pml

----------------------------------------------------------------------------------------------------------
We have developed two models

model 1: 
Parses C code with regex‑based detectors and a context stack to identify types, functions, and control flow.
Generates corresponding Promela typedefs, proctypes, channels, loops, and heap models to mirror the original C behavior(little primitive than model 2)

model 2:
Parses the C source into an AST using pycparser and collects types, structs, and functions.
Traverses each AST node to emit equivalent Promela proctypes, memory pools, and control‐flow constructs.
