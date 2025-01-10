# Proving equivalence of $d$-separation and conditional independence

## Definitions

- A path is **$d$-connected** given set of nodes $Z$ if
  - for all mediators $m$ on the path, $m \not\in Z$
  - for all confounders $c$ on the path, $c \not\in Z$
  - for all colliders $c$ on the path, there exists some descendant $d$ of $c$ such that $d \in Z$
- Two nodes $u$ and $v$ are **$d$-separated** given $Z$ if no path from $u$ to $v$ is $d$-connected

## Semantics

- Each node $v$ is defined by a function $f_v$. In other words, the value of $v$ is given by $$f(v) = f_v(pa_v, u_v) = f_v([f(p_1), f(p_2), ..., f(p_k)], u_v)$$
  - $pa_v$: values of $p_1, ..., p_k$, the parents of $v$
  - $u_v$: some error term for $v$
- Two nodes $u$ and $v$ are **independent** conditioned on $Z$ if $f(v)$ is unaffected by $f(u)$, given that we know the values of nodes in $Z$ beforehand
- Formally, for all values $a, b$, $f(v)$ stays constant regardless of whether $f(u) = a$ or $f(u) = b$

```coq
forall (g: graphfun),
(forall (w: node),
    In w Z -> find_value G g w U = get_assigned_value A w)
-> forall (a b x: X),
(find_value G g u U = Some a -> find_value G g v U = Some x) ->
(find_value G g u U = Some b -> find_value G g v U = Some x).
```

## Independent $\Rightarrow$ $d$-separated

- Show that for each path, $d$-connected $\Rightarrow$ _not_ independent. Then, we have independent $\Rightarrow$ for all paths, not $d$-connected $\Rightarrow$ $d$-separated
- First show for 3-node paths with a mediator, confounder, and collider
- Use induction to extend to arbitrary length path
- Main idea: choose a specific $g$ to force $f(v)$ to depend on (often be equal to) $f(u)$

### Mediator: $u \rightarrow m \rightarrow v$

- Choose $f_v$ such that $f_v(pa_v, u_v) = f_v([..., f(m), ...], u_v) := f(m)$
- Similarly, set $f_m(pa_m, u_m) := f(u)$
  - _Not explicitly using $d$-connected assumption. Can we choose a function for $m$ even if $m \in Z$?_
- This forces $f(v) = f(u)$, so $u$ and $v$ cannot be independent

### Confounder: $u \leftarrow c \rightarrow v$

- Choose $f_v$ such that $f_v(pa_v, u_v) = f_v([..., f(c), ...], u_v) := f(c)$
- Similarly, set $f_u(pa_u, u_u) := f(c)$
- This forces $f(v) = f(u)$, so $u$ and $v$ cannot be independent
  - _This is using that $f(c)$ could take on at least 2 different values. Can we assume this if $c \not\in Z$?_

### Collider: $u \rightarrow c \leftarrow v$

- Since the path is $d$-connected, there is some descendant $d$ of $c$ such that $d\in Z$, so $f(d) = x$ always.

<p align="center">
<img src="graphs/collider.JPG" alt="collider" style="width:200px;"/>
</p>

- Choose $f(d) := f(d_k)$, ..., $f(d_2) := f(d_1)$, $f(d_1) := f(c)$
- Choose $f_c$ to force $f(u)$ and $f(v)$ equal:
  $$
  f_c(pa_c, u_c) = f_c([,..., f(u), ..., f(v), ...], u_c) =
  \begin{cases}
  x & f(u) = f(v)\\
  y & \text{else}
  \end{cases}
  $$
  This would ensure that $f(u)=f(v)$, or else a contradiction ($x \neq y$)
- Challenges:
  - Have to prove that changing the function for a node doesn't affect pre-existing the relationships between other node functions

### Arbitrary length path: $u \leftrightarrow u_1 \leftrightarrow u_2 \leftrightarrow \cdots \leftrightarrow u_k \leftrightarrow v$

- Base case is above three cases
- Induction step: assuming that there exists some graph function that makes $f(u_1) = \cdots = f(u_k) = f(v)$, show the same for $f(u)$.
- Basically use casework to see which of the above cases $u \leftrightarrow u_1 \leftrightarrow u_2$ falls into
- Challenge is modifying the graph function in a way that preserves existing equalities

<p align="center">
<img src="graphs/gencase1.JPG" alt="gencase1" style="width:500px;"/>
</p>
<p align="center">
<img src="graphs/gencase2.JPG" alt="gencase2" style="width:500px;"/>
</p>

- Might have to make a more general notion of node function affected by (?) other node function, rather than just strictly equal

## $d$-separated $\Rightarrow$ independent

### Easy case: the only path between $u$ and $v$ is $u \rightarrow m \rightarrow v$, and $m$ is the only parent of $v$

- Since $u, v$ are $d$-separated, $m \in Z$, so $f(m) = x$ always. Then, $f(v) = f_v(pa_v, u_v) = f_v([x], u_v)$, which is constant, so clearly $v$ is independent from $u$
- Since the definition of independence has to hold for all $a, b, x$, there's nothing that can show $f(u) = a$ (or maybe it never equals $a$)
  - _Should the definition of independence be reformulated?_

```coq
a, b, x: X
H1: f(u) = a -> f(v) = x
H2: f(u) = b
--
f(v) = x
```

### Slightly harder mediator case: the only path between $u$ and $v$ is $u \rightarrow m \rightarrow v$

- Now, $f(v) = f_v(pa_v, u_v) = f_v([..., x, ...], u_v)$
- Intuitively, the other parent values $f(p)$ can't depend on $u$, or else there must be a path from $u$ to that path (contradiction, because then there is a different path from $u$ to $v$). But this is hard to formally prove
  - Lemma: if there are no paths between nodes $w, x$, then $w, x$ are independent
  - From the lemma, can conclude that $u, p$ are independent (if not, then there must be a path between them, resulting in another path between $u, v$)

### General case: $u$ and $v$ are $d$-separated

- Harder, probably induction (or maybe prove not independent $\Rightarrow$ $d$-separated?)
- Now $u, p$ don't have to be independent -- there could be a path from $u \leftrightarrow \cdots \leftrightarrow p \leftrightarrow \cdots v$. We know that it's blocked, but we don't know where ($p$ could totally depend on $u$)
