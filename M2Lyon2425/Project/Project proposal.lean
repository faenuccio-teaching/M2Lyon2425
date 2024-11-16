/- Good evening, I am very sorry I am this late in submitting my idea for the project, but since it involved topology, I wanted to wait for the first class about topological spaces, which was two days ago.
I mistakenly assumed that what you were asking us to do here was to already give an outline of the Lean tactics that we would use for the project. After talking with Prof. Morel yesterday I learnt that 
was not the case. So here I come with my idea, which, in fact, would be to formalize a famous result from topology.

I would like to take on part of the proof of Van Kampen's theorem. I would have the following statement:
``Let X be a topological space, and let A,B \subseteq X two open subsets of X such that:
1) A, B, and A \cap B are path connected
2) A \cup B = X
Let x_0 \in A \cap B, f: A \to X, g: B \to X the inclusion maps. Let P_A = \pi_1 (A,x_0), P_B = \pi_1 (B,x_0), P_AB = \pi_1 (A \cap B,x_0), P = \pi_1 (X,x_0) the fundamental groups of A, B, A \cap B, X centered in x_0.
Let f_\ast, g_\ast be the images of f and g under the functor \pi_1 : Pointed Top Spaces \to Groups. Let's call * the junction between two paths \alpha and \beta on X such that \alpha(1) = \beta(0). 
So (\alpha * \beta): [0,1] \to X, (\alpha * \beta)(t) = \alpha(2*t) if t \leq 1/2, (\alpha * \beta)(t) = \beta(2*t-1) if t \geq 1/2. For each path \delta on X let's call inv(\delta) the inverse path,
meaning inv(\delta): [0,1] \to X, inv(\delta)(t) = \delta(1-t). 
Let P_A \ast P_B be the free product of P_A and P_B (so the coproduct in the category of Groups), and \ast be the free product operation in this group. Then the function \phi: P_A \ast P_B \to P that sends 
\alpha_1 \ast \beta_1 \ast \cdots \ast \alpha_n \ast \beta_n to f_\ast (\alpha_1) * g_ast (\beta_1) * \cdots * f_\ast (\alpha_n) * g_\ast (\beta_n) (which is the one deriving by the universal property of 
the coproduct in the Group category) is surjective.
Also , if i_1 : A \cap B \to A and i_2 : A \cap B \to B are the inclusion maps, j_1: P_A \to P_A \ast P_B and j_2: P_B \to P_A \ast P_B are the canonical maps for the coproduct, 
and i_{1_\ast}, i_{2_\ast} are the images of i_1 and i_2 under the functor \pi_1, then we have \{j_1(i_{1_\ast}(\alpha)) * j_2(i_{2_\ast}(inv(\alpha))), \alpha \in P_AB\} \subseteq Ker(\phi).''

Actually, this last inclusion is an equality, but proving the other inclusion is already hard enough in regular math classes, so I don't think it would be a good idea to also formalize that part of the Van Kampen theorem.

The proof I have of this theorem starts from a preliminary lemma, with the following statement: 
``Let X be a topological space, and \mathcal{A} an open covering of X. Let \alpha : [0,1] \to X be a path on X. Then there exists a positive integer n such that, \forall i \in \{0,\ldots,n-1\}, there exists a 
B_i \in \mathcal{A} such that \alpha ([\frac{i}{n}, \frac{i+1}{n}]) \subseteq B_i''. The proof of this preliminary lemma is as follows:

``For each B \in \mathcal{A}, we have that \alpha^{-1}(B) is an open set in [0,1], thus given by disjoint unions of open real intervals, which are in turn intersected with [0,1]. 
Consider then the set \mathcal{B} = \{I \subseteq [0,1] such that I is open, and there exists B \in \mathcal{A} such that I is a connected component of \alpha^{-1}(B)\}. Since \mathcal{A} is an open covering of X
and the union of all sets in \mathcal{B} is the same as the union of all elements of \{\alpha^{-1}(B) such that B \in \mathcal{A}\}, then \mathcal{B} is an open covering of [0,1]. Since [0,1] is compact, we may then exctract
a finite subcovering from \mathcal{B}, let's call it \mathcal{C}. Each element of \mathcal{C} is an open connected subset of [0,1], and is also a connected component of some \alpha^{-1}(B), for B \in \mathcal{A} by definition.
We can then say that \forall I \in \mathcal{C}, \exists B \in \mathcal{A} such that \alpha(I) \subseteq B. Now consider the biggest interval \in \mathcal{C} that contains 0, I_0. If that interval is [0,1] then we are done,
setting n = 1. If that interval is [0,x1) then consider the intervals \in \mathcal{C}\setminus \{I_0\} that contains x1, I_1. This intervals will be of the form (x1-\lambda_1,1] or (x1-\lambda_1, x1+\rho_1), with \lambda_1 > 0,
\rho_1 > 0. Select the one with the biggest right bound. In both cases we have that [0,x1) \cap I_1 \neq \emptyset. If appliable, call x2 = x1+\rho_1. Continue this process until we find an interval I_k that contains 1. 
This is possible because \mathcal{C} contains finitely many intervals, and at each step we progressively remove them one by one. We now have open intervals I_0,\ldots,I_k such that I_{i-1} \cap I_{i} \neq \emptyset 
for all i \in \{1,\ldots,k\}. Set n such that 1/n is smaller than all intervals I_{i-1} \cap I_i, for all i \in \{1,\ldots,k\} (which are a finite number). Then each interval [j/n, (j+1)/n] is a subset of a specific I_i, 
for all j \in \{0,\ldots,n-1\}, this can be proved by induction on j. 
The interval [0, 1/n] is included in I_0, as I_0 is bigger than I_0 \cap I_1, which means x1 = |x1 - 0| > 1/n = |1/n - 0|, and thus [0,1/n] \subseteq [0,x1) = I_0. Now suppose that [(j-1)/n, j/n] is included into some I_i.
Suppose i < k. If [(j-1)/n,j/n] \cap (I_i \cap I_{i+1}) = \emptyset, then the set I_i \cap [j/n, 1] strictly contains (I_i \cap I_{i+1}), thus if g = sup (I_i \cap I_{i+1}), |g-j/n|> 1/n = |(j+1)/n - j/n|. As such,
[j/n, (j+1)/n] \subseteq I_i. If [(j-1)/n, j/n] \cap (I_i \cap I_{i+1}) \neq \emptyset, then j/n \in (I_i \cap I_{i+1}). If i+1 = k, then [j/n, (j+1)/n] must be a subset of I_k, as I_k is the interval containing 1,
and (j+1)/n \leq 1. If i+1 < k, we have that j/n cannot be contained into (I_{i+1} \cap I_{i+2}). This is because j/n < x_{i+1}, and if it were part of I_{i+2}, then x_{i+1} would also be part of that interval.
This contradicts our choice for the interval I_{i+1} as the one containing x_{i+1} that had the greatest right bound (I_{i+2} has an even greater right bound, as it contains x_{i+2} that wasn't contained into I_{i+1}).
Thus [j/n, 1] \cap I_{i+1} contains (I_{i+1} \cap I_{i+2}), and following the same reasoning applied before, we have [j/n, (j+1)/n] \subseteq I_{i+1}. If i = k, then I_i contains 1. If j = k there is nothing to prove, 
if j < k then (j+1)/n \leq 1, so [j/n, (j+1)/n] \subseteq I_k. So now we successfully partitioned [0,1] into intervals [j/n, (j+1)/n] such that each of them is contained into one respective I_i. But each I_i is such that
\alpha (I_i) is contained into one of the open sets of \mathcal{A}. For all j, consider B_j as the open set in \mathcal{A} that contains \alpha(I_i), where [j/n, (j+1)/n] \subseteq I_i. 
We have then found our partition, such that \alpha ([\frac{j}{n}, \frac{j+1}{n}]) \subseteq B_j, as we wanted.''

Given this preliminary lemma, the proof of the Van Kampen theorem as stated above is as follows:

``Let \alpha be a loop in X with base point x_0. Then, since A and B are open, by the lemma there exists a positive integer n such that, for all i \in \{0,\ldots,n\} \alpha([i/n, (i+1)/n]) \subseteq A or
\alpha([i/n,(i+1)/n]) \subseteq B. Let's call, for each i, x_i = \alpha(i/n). x_0 found this way is exactly the x_0 appearing in the hypothesis, as it is the base point of \alpha, and it is also equal to x_n.
Let's define, for each 0\leq i < n, a path from x_i to x_{i+1}, which is \alpha_{i}: [0,1] \to X such that \alpha_i(t) = \alpha (\frac{i+t}{n}). Now, consider one x_i. If x_i \in A \cap B, since A \cap B is path connected,
we can define a path \beta_i: [0,1] \to A \cap B from x_i to x_0 (we define the paths \beta_0 and \beta_n will just be the trivial path). If x_i \in (A \setminus B), since A is also path connected, we may define a path
\beta_i: [0,1] \to A from x_i to x_0. If x_i \in (B \setminus A), since B is also path connected, we may define a path \beta_i: [0,1] \to B from x_i to x_0.
Let's now define paths \gamma_1,\ldots,\gamma_n in the following way. For each i \in \{0,\ldots,n-1\} \gamma_{i+1} = inv(\beta_{i}) * \alpha_i * \beta_{i+1} (remember \beta_0 and \beta_n are the trivial paths).
Each of these paths is a loop with base point x_0, and by construction each of them has its image completely in A or completely in B. Furthermore, \gamma_1 * \gamma_2 * \cdots * \gamma_n = 
= inv(\beta_0) * \alpha_0 * \beta_1 * inv(\beta_1) * \alpha_1 * \beta_2 * \cdots * \beta_{n-1} * inv(\beta_{n-1}) * \alpha_{n-1} * \beta_n = \alpha_0 * \alpha_1 * \cdots * \alpha_{n-1} = \alpha by construction.
As the \gamma_i paths are either entirely in A or entirely in B each, each of them is either in P_A or in P_B, while \alpha is in P. We have thus shown that each \alpha \in P can be written as the image under \phi of 
\gamma_1 \ast \gamma_2 \ast \cdots \ast \gamma_{n-1}, and can conclude that \phi is surjective, as we wanted.
As for the second part of the theorem, we start by noting that f \comp i_1 = g \comp i_2, as they are both the inclusion map from A \cap B to X. Since \pi_1 is a functor, then, f_\ast \comp i_{1_\ast} = g_\ast \comp i_{2_\ast}.
Now, the universal property of coproducts also tells us that f_\ast = \phi \comp j_1 and g_\ast = \phi \comp j_2. Let then \alpha \in P_AB. We have f_\ast \comp i_{1_\ast} (\alpha) = g_\ast \comp i_{2_\ast} (\alpha),
which means \phi(j_1(i_{1_\ast} (\alpha))) = \phi(j_2(i_{2_\ast} (\alpha))), which implies j_1(i_{1_\ast}(\alpha)) * inv(j_2(i_{2_\ast}(\alpha))) = 1. Since, given \delta\in P, inv(\delta) is actually the inverse of 
\delta in the group P, with binary operation *, and since j_2 and i_{2_\ast} are group homomorphisms, we may conclude j_1(i_{1_\ast}(\alpha)) * j_2(i_{2_\ast}(inv(\alpha))) = 1, so 
j_1(i_{1_\ast}(\alpha)) * j_2(i_{2_\ast}(inv(\alpha))) \in Ker(\phi), as we wanted.''

I tried to expand these proofs with as many details as I could, since these would also probably be required steps to do when formalizing. I am still missing a big portion of knowledge on which tactics I could
be using on Lean to actually prove all this stuff, and in topology class when we went over these proofs a lot was actually left as exercise or skipped because it was intuitive (which is a common thing to do in topology).
I am therefore asking you if some doable project could be extracted from these theorems and their proofs that I have just written above, maybe if my initial idea was too ambitious I can prove only part of the things stated
above. If there are things that I introduced here that would be too hard to use on Lean (I'm thinking about the definition of fundamental group, and its usage as a functor, or the characterizations of open sets in [0,1])
please let me know, and I will think of something more feasible.
Thank you for your attention.
Kind regards,
Andrea Iacco
-/
