# Practical Intro to Agda and Coq

This repo contains the materials for my talk at
[HaskellerZ meetup](https://www.meetup.com/HaskellerZ/events/270704738/).

I created some installation instructions for those of you who'd want
to follow along but don't have Agda or Coq set up yet. I also created
a Docker image with everything configured properly. The image is a bit
heavy (1GB compressed), but is probably the fastest way to get going,
and is very easy to clean up afterwards. ;)

https://github.com/nilcons/agda-coq-setup

# Quick pointers for the live coding, Agda

This [official quick guide](https://agda.readthedocs.io/en/v2.6.1/getting-started/quick-guide.html)
contains the most important commands and tips for working with agda, keep it open.
(For a bit more details consult [this](https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html).)

In addition to the above:

- If you want to know how to enter a Unicode character (which you have
  an example of somewhere), do `M-x quail-show-key` while standing on it
- Look up a Unicode character by its Unicode name (fuzzy search): `C-x 8 RET`
- Write `-l` into a hole and type `C-c C-a` to make Agda list some
  terms that would “fit” in the hole.


# Quick pointers for the live coding, Coq

Emacs commands:

- `C-c C-n`: check next statement
- `C-c RET`: check up to the current position
- `C-c C-b`: check the whole buffer
- `C-c C-x`: quit Coq and kill its windows

Useful Coq commands:

- `Print x.` Print the definition of x.
- `Check expression.` Type check an expression and print its type.
- `Compute expression.` Evaluate (fully normalize) an expression.
- `Set Printing All.` Turn off all syntactic sugar and show all
  implicits.

# Learning

Software Foundations: https://softwarefoundations.cis.upenn.edu/

Certified Programming with Dependent Types: http://adam.chlipala.net/cpdt/

