# I/O Logic Workbench
*A browser-based automated reasoner for Input/Output Logics*

Input/Output (I/O) logics have been devised by Makinson and van der Torre [1]
as a class of formal systems for norm-based deontic reasoning. Intuitively,
they formalize the question what obligations can be detached (the output) from a given
set of conditional norms and a specific situation (the input). It differs from
other deontic logics in the sense that the norms themselves are not part of the
object logic and hence do not carry truth values.

## The Tool

The I/O Logic Workbench is aimed at providing a browser-based automated reasoning system for various I/O logics.
In short, the system allows you to input a set of norms and an input (the description of the current situation),
and provides automated means for inferring whether a certain formula can be derived as an obligation from this.
See [Usage](#usage) below for details.

It is implemented as a client-side application in JavaScript, so that there is no
need for any backend server infrastructure. Hence, it runs in every reasonably current browser,
ready-to-use for conducting own experiments without any major installation or set-up.

## Installation

The Workbench does not require any form of installation. Just download the source code package (e.g. as a .zip archive)
from here, unpack it and open the `index.html` in any reasonably modern browser of your choice.


## Usage

The Workbench looks like this (depending a bit on your browser):

![The I/O Logic Workbench](/doc/iolw.png)

The graphical user interface consists of two main panels: The configuration panel (on the left)
and the main panel (on the right):

<img alt="The configuration panel" src="/doc/left.png" width="300">

In the left menu panel, a user can choose which out operation should be used for the reasoning process.
Please note that there are already some disabled configuration settings that are not yet supported.
Additionally, some example scenarios can be loaded using the respective buttons at the top left.

![The main panel](/doc/right.png)

On the right side, the input A, the set of norms N and a prospective output
x can be entered. The input language is an ASCII representation of propo-
sitional logic, where |, & and  ̃  denote disjunction, conjunction and negation,
respectively. The input A is a comma separated list of formulas, whereas the
set of norms N is, as usual, represented as a set of pairs. Every norm is entered
as a separate line in the text area. 

To check whether a formula is in the output set of the selected out operator, enter the respective
information for A, N and x and press "check given output".

## Roadmap / Version history

- [X] Unconstrained I/O logic (since 0.1)
- [X] Throughput (since 0.2)
- [ ] Constrained I/O logic
- [ ] Calculation of finite basis of output set
- [ ] Norm preferences

Current version: 0.3
Last update: Some bug fixes and beautification of graphical interface.

## References

[1] Makinson, D., van der Torre, L.W.N.: Input/Output Logics. J. Philosophical Logic 29(4), 383–408 (2000). https://doi.org/10.1023/A:1004748624537
