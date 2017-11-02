# An McClim App for viewing SBCL IR1 flow graph

## TODOs
- Try to see if it still works against the latest McClim/SBCL/Linux.
- Find some road to a modern CI approach.
- No Spaghettis, Split the code and improve it!
- No implicit tricky modification to the compilation process.
- Improve the rendered images of flow graph.
- Generate animation depicting the difference before/after each optimization.

## Note
**This project was a toy project for understanding the process and result of ir1 compilation of SBCL.**
**To run it, you have to compile SBCL yourself to a particular debug version.**
**To keep the structure of generated flow graph as similar to the source code as possible, some optimization are intendedly cancelled by hacking SBCL directly. This method is tricky and error-prone.**
