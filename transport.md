**1. Assign a current to each edge.** For radius $k$, let $L=2k+1$. Number the vertices of the larger interval from 0 to $L+1$. Multiply the paper's currents and masses by the positive denominator $L(L+2)$. The current on edge $t$ becomes $2t-L$ for $0\le t\le L$, and is zero outside.

**2. Check mass balance.** At each of the two new endpoints the outgoing current minus the incoming current equals $-L$. At each old vertex it equals 2. Outside the interval it vanishes. These are exactly the differences between the two scaled uniform mass functions.

**3. Bound the energy.** Each of the $L+1$ edge currents has absolute value at most $L$. Summing squares and dividing by the square of the common denominator gives at most $(L+1)/(L+2)^2$, which is at most $1/(k+1)$. Lean checks the equivalent integer inequality for every natural $k$.

**4. Remaining paper argument.** For higher dimensions the paper expands one coordinate at a time, weights each one-dimensional flow by the mass of its coordinate line, and adds their energies. These steps remain open in Lean.
