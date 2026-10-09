# A Characteristic-Zero Counterexample to Tachikawa's Second Conjecture

Tachikawa's second conjecture, in its symmetric characteristic-zero formulation, asks whether vanishing of all positive self-extension groups forces a module to be projective.

> [!NOTE]
> **Conjecture (Tachikawa's second conjecture, symmetric case over $\mathbb Q$).**
>
> Let $\Gamma$ be a finite-dimensional symmetric $\mathbb Q$-algebra and let $M$ be a finite-dimensional left $\Gamma$-module. If
>
> $$
> \mathrm{Ext}^i_\Gamma(M,M)=0\qquad\text{for every }i>0,
> $$
>
> then $M$ is projective.

Here symmetric means that $\Gamma$ and its rational dual are isomorphic as $\Gamma$-bimodules. Tensor products without a subscript are over $\mathbb Q$, and $D=\mathrm{Hom}_{\mathbb Q}(-,\mathbb Q)$.

This repository presents a proposed counterexample for **Formal Conjectures**: a symmetric rational algebra $\Gamma$ and a finite nonprojective module $M$ satisfying the displayed vanishing. The argument is outlined below and given in full in the [PDF manuscript](PDF/tachikawa-characteristic-zero.pdf).

## Proof sketch

### 1. Construct the rational starting algebra

Let $C$ have basis $(e,f,x,y,z,u,v,t,j,n)$, with orthogonal idempotents $e+f=1$ and corners

$$
eCe=\langle e,x,y,z\rangle,\quad eCf=\langle u,v\rangle,\quad
fCe=\langle t,j\rangle,\quad fCf=\langle f,n\rangle.
$$

The nonzero products of radical basis elements are

$$
\begin{array}{llll}
xy=2z,&yx=z,&xu=v,&yu=v,\\
ut=y+2x,&uj=z,&un=v,&vt=2z,\\
tx=j,&ty=4j,&tu=3n,&nt=2j.
\end{array}
$$

Let $s$ be the one-dimensional character supported at $f$, and put $\ell_i=x-(-2)^i y$. Right multiplication gives a projective resolution

$$
R_0=Cf,\qquad R_i=Ce\ (i\ge1),\qquad
d_1=\rho_u,\qquad d_{i+2}=\rho_{\ell_i}\ (i\ge0).
$$

The kernels and images can be computed in the displayed basis for every index. They give $\mathrm{Ext}^{i}_C(s,s)=0$ for $i>0$ and

$$
H^a\mathrm{Hom}_C(R,C)=
\begin{cases}Ds&a=2,\\0&a\ne2.\end{cases}
$$

Explicit finite resolutions also give projective dimension at most two for $DC$ on both sides.

### 2. Compute stable extensions and the scaling actions

Set $T=C\ltimes DC$, $E=T\otimes T$, and $X=s\otimes s$. The algebras $T$ and $E$ are symmetric, of dimensions $20$ and $400$. The induced complex $\mathcal J=T\otimes_C R$ fits into a triangle

$$
s[2]\longrightarrow\mathcal J\longrightarrow s
\xrightarrow{\tau}s[3].
$$

The associated long exact sequence gives $\mathrm{Ext}_T^*(s,s)=\mathbb Q[\tau]$, with $|\tau|=3$. The signed tensor product then gives

$$
\mathrm{Ext}_E^*(X,X)=
\mathbb Q\langle\tau_1,\tau_2\rangle/
(\tau_1\tau_2+\tau_2\tau_1).
$$

Write $\mathcal P_m=\langle\tau_1^a\tau_2^b:a+b=m\rangle$. Symmetric stable duality determines all negative degrees as well:

$$
\mathcal H^{3m}=\mathcal P_m,\qquad
\mathcal H^{-3m-1}=D\mathcal P_m\qquad(m\ge0),
$$

where $\mathcal H^a=\underline{\mathrm{Hom}}_E(X,X[a])$ and all other groups vanish. The shift $[1]$ denotes inverse syzygy.

For $H\in\mathbb Q^\times$, let $h_H(a,\phi)=(a,H\phi)$ on $T$, and let $U_H=E_{h_H\otimes h_H}$ denote the right-twisted regular bimodule. Its tensor functor fixes $X$ and acts on the two families of stable groups by

$$
H^{-m}\quad\text{in degree }3m,\qquad
H^{m+2}\quad\text{in degree }-3m-1.
$$

The negative weight follows from the action $H^2$ on the degree-minus-one socle class and the composition pairing with positive extensions.

### 3. Obtain bimodule maps from a twisted trace obstruction

The diagonal map

$$
\sigma_0(e,f,x,y,z,u,v,t,j,n)
=(e,f,-x,-y,z,u,-v,-t,j,-n)
$$

is an involutive automorphism of $C$. For every $a\in C$, the multiplication table gives

$$
\mathrm{tr}(L_aR_f\sigma_0^{-1})=0.
$$

Put $B=C\otimes C$ and $\theta_0=\sigma_0\otimes\sigma_0$. If $\chi_B$ is the character of $s\otimes s$, the bimodule map

$$
\eta:B_{\theta_0}\longrightarrow DB,\qquad
\eta(a)=\chi_B(a)\chi_B
$$

cannot factor through a perfect bimodule complex. Indeed, the finite injective-dimension bound reduces such a factorization to ordinary maps through finite sums and summands of $DB\otimes B$. Evaluation at $f\otimes f$ then gives a twisted trace, hence zero, whereas $\eta(1)(f\otimes f)=1$.

Derived induction and stable duality turn this obstruction into a finite bimodule $Y$, projective separately on the left and right, and maps $g_H:U_H\to Y$ whose evaluations at $X$ are stably nonzero. The signed Koszul sequence for $\tau_1,\tau_2$, together with its negative-degree dual, gives

$$
W^a:=\underline{\mathrm{Hom}}_E(X,(Y\otimes_E X)[a])=
\begin{cases}\mathbb Q&a=-3,0,\\0&\text{otherwise}.\end{cases}
$$

### 4. Combine the two twists and form a triangular cone

Take $H=2,3$ and rescale $g_2,g_3$ so that their evaluated stable classes agree. Choose a finite free bimodule $Q$ with a surjection $\pi:Q\to Y$, and define $F$ by

$$
0\longrightarrow F\longrightarrow U_2\oplus U_3\oplus Q
\xrightarrow{(g_2,-g_3,\pi)}Y\longrightarrow0.
$$

This sequence splits on each side. The normalized common class gives a stable map $v:X\to F\otimes_E X$ projecting to $(1,1)$. The resulting comparison maps are

$$
\Delta^a(g,h)=F(g)v-v[a]h.
$$

On the supported positive and negative degrees, projection to the two twists identifies these maps with

$$
\begin{pmatrix}2^{-m}&-1\\3^{-m}&-1\end{pmatrix}
\quad(m\ge1),\qquad
\begin{pmatrix}2^{m+2}&-1\\3^{m+2}&-1\end{pmatrix}
\quad(m\ge0),
$$

tensored with the identity on the corresponding stable group. Their determinants are nonzero. The remaining boundary maps are a surjection in degree zero and the injection $0\to\mathbb Q$ in degree $-2$.

Over the triangular algebra

$$
\Lambda=\begin{pmatrix}E&0\\F&E\end{pmatrix},
$$

lift $v$ to a map between the two column complexes of a complete resolution of $X$, and take its mapping cone $P_Z$. Its degree-zero cokernel $Z$ is finite and nonprojective. The full endomorphism complex has connecting maps $\Delta^a$, so their kernels and cokernels give

$$
H^a\mathrm{Hom}_\Lambda(P_Z,Z)=
\begin{cases}\mathbb Q&a=-1,0,\\0&\text{otherwise}.\end{cases}
$$

### 5. Transfer to a symmetric algebra

Set

$$
\Gamma=\Lambda\ltimes D\Lambda,\qquad
M=\Gamma\otimes_\Lambda Z.
$$

Total acyclicity of $P_Z$ makes $D\Lambda\otimes_\Lambda P_Z$ exact. Thus $\Gamma\otimes_\Lambda P_Z$ is an exact complex of finite projective $\Gamma$-modules resolving $M$ in nonnegative degrees.

For $N=D\Lambda\otimes_\Lambda Z$, the negative tail supplies an injective coresolution and gives

$$
\mathrm{Ext}_\Lambda^i(Z,N)
\cong D H^{-i-1}\mathrm{Hom}_\Lambda(P_Z,Z)=0
\qquad(i>0).
$$

Induction-restriction adjunction therefore yields

$$
\mathrm{Ext}_\Gamma^i(M,M)
\cong\mathrm{Ext}_\Lambda^i(Z,Z\oplus N)=0
\qquad(i>0).
$$

The trivial extension $\Gamma$ is symmetric. If $M$ were projective, applying $\Lambda\otimes_\Gamma-$ to a split free presentation would make $Z$ projective, a contradiction. This gives the required finite nonprojective self-orthogonal module over $\mathbb Q$.

## Detailed manuscript

- [PDF manuscript](PDF/tachikawa-characteristic-zero.pdf)

Public draft 1, 9 October 2026.
