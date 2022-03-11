(*<*)
theory ResumenHall
  imports
  Main
  Marriage
"TeoriaCompacidad"
(*
"/home/usuario/Escritorio/Teorias/TeoremaCompacidad/TeoriaCompacidad"
"/Teorias/TeoremaCompacidad/TeoriaCompacidad" *)
begin
(*>*)
section \<open>Teorema de Hall\<close>
text\<open>
Sea $\mathcal{A}$ una familia finita  de subconjuntos arbitrarios de un conjunto $S$ tal que los
conjuntos de la colección  pueden repetirse.
El teorema de Hall (teorema del matrimonio) demostrado por Philip Hall en 1935 \textcolor{blue}{\cite{Hall}},
establece una condición necesaria y suficiente para poder seleccionar  de cada conjunto de la colección
un elemento distinto. Este teorema es equivalente a otros seis resultados importantes que se aplican
en el estudio de problemas combinatorios y de teoría de grafos \textcolor{blue}{\cite{Borgersen}}: 
teorema de Menger (1929),
teorema de König para matrices (1931), el teorema König–Egerváry (1931),
 el teorema Birkhoff-Von Neumann (1946), teorema de Dilworth’s (1950) y el teorema del flujo máximo
y corte mínimo, Max Flow-Min Cut (algoritmo de Ford-Fulkerson) (1962). 
\par
La manera usual de enunciar el teorema de Hall es utilizando el concepto de
{\emph{sistema de representantes distintos}} para una familia de conjuntos.
\<close>

text\<open>
\begin{definicion}
Sean  $S$ un conjunto y $\{S_i\}_{i\in I}$ una colección de subconjuntos de $S$ (no necesariamente distintos)
con índices en el conjunto $I$.
\par
Una sucesión
$(x_i)_{i\in I}$ es un sistema de representantes distintos (SRD) para 
$\{S_i\}_{i\in I}$ si, 
\begin{enumerate}
\item Para todo $i \in I$, $x_i\in S_i$, y
\item Para todo $i,j\in I$, si $i\neq j$ entonces $x_i\neq x_j$.
\end{enumerate}
En forma equivalente,
\par
Una función $f:I\to   \bigcup_{i\in I}S_i$ es un SRD para $\{S_i\}_{i\in I}$ si,
\begin{enumerate}
\item Para todo $i \in I$, $f(i)\in  S_i$, y
\item $f$ es inyectiva.
\end{enumerate} 
\end{definicion}
\<close>

text\<open>
\begin{teorema}[Teorema de Hall, caso finito]\label{HallFinito}
Sean $S$ un conjunto y $n$ un entero positivo. Una colección 
$\{S_1,S_2,\ldots , S_n\}$ de subconjuntos de $S$ tiene un SRD si y solamente si:
\par
 (M) Para cualquier $1\leq k \leq n$ y cualquier elección de $k$ índices distintos
 $1\leq  i_1, \ldots , i_k \leq n$, se tiene que
  $|S_{i_1}\cup \ldots  \cup S_{i_k}|\geq k$. 
\end{teorema} 
La condición $(M)$ para la existencia de un SRD es llamada la {\emph{condición de matrimonio}}.
\<close>
text\<open>
El teorema sigue siendo válido si la colección $\{S_i\}_{i\in I}$ es una familia enumerable de conjuntos 
finitos; otros casos son considerados y probados  en \textcolor{blue}{\cite{Rado}}. 
\<close>
text\<open>
\begin{teorema}[Teorema de Hall, caso infinito enumerable]\label{HallInfinito}
Sea $S$ un conjunto. Una colección $\{S_n\}_{n\in \mathbb{N}^{+}}$ de 
subconjuntos finitos de $S$, tiene un SRD si y solamente si:
\par
 ($M^{ * }$) Para cualquier $k \in \mathbb {N}^{+}$ y cualquier elección de $k$ índices distintos
 $i_1, \ldots , i_k \in \mathbb{N}^{+}$, se tiene que
  $|S_{i_1}\cup \ldots \cup S_{i_k}|\geq k$.  
\end{teorema}
\<close>
text\<open>
Una descripción de la formalización en Isabelle/HOL del teorema de Hall para el caso finito 
$\{S_1,S_2,\ldots , S_n\}$ en el que además los $S_i$  son finitos,
aparece en Jiang y Nipkow \textcolor{blue}{\cite{Marriage-AFP}}. 
En este trabajo formalizamos en Isabelle/HOL, para el  caso infinito enumerable, la  
 suficiencia de la condición de matrimonio para la existencia de un SRD, $M^{ * }\Rightarrow \text{SRD}$.
La demostración utiliza la formali\-zación de la versión finita de Jiang y Nipkow
 \textcolor{blue}{ \cite{DBLP:conf/cpp/JiangN11}} y el Teorema de Compacidad, y está guiada por la 
siguiente prueba informal.
\<close>
text\<open>
{\bf{Prueba informal:}} Supongamos que la condición ($M^{ * }$) se cumple.
\par
Consideremos el lenguaje proposicional con símbolos proposicionales el conjunto,
 $$\mathcal{P} = \{C_{n,x} \mid n\in \mathbb{N}^{+}, x\in S_{n} \}$$
 donde $C_{n,x}$ es interpretado como ``se selecciona el elemento $x$ del conjunto $S_{n}$''.
Los siguientes tres conjuntos de proposiciones permiten describir la existencia de un SRD para 
$\{S_i\}_{i\in I}$.
\begin{itemize}
\item[1.] Se selecciona por lo menos un elemento de cada $S_n$:
$$ \mathcal{F} =
 \{\vee_{x\in S_{n}} C_{n, x}\mid n\in \mathbb{N}^{+}\},$$
donde  $\vee_{x\in S_{n}}C_{n, x}$ es la disyunción de las fórmulas atómicas correspondientes a los
elementos del conjunto  $S_{n}$, el cual por hipótesis es finito.
\par
\item[2.] Se selecciona a lo más  un elemento de cada $S_n$:
$$ \mathcal{G} =\{ \neg (C_{n,x}\wedge C_{n,y})\mid  x, y \in S_n, x\neq y, n \in \mathbb{N}^{+}\}.$$
\item[3.] No se selecciona  más de una vez un mismo elemento de  $\bigcup_{n \in \mathbb{N}^{+}}S_n$:
$$ \mathcal{H} =\{\neg (C_{n,x}\wedge C_{m,x})\mid x\in S_n\cap S_m, n \neq m,  n, m\in \mathbb{N}^{+} \}.$$

\end{itemize}

Sea  $\mathcal{T} = \mathcal{F}  \cup \mathcal{G} \cup \mathcal{H}$, aplicamos el Teorema de Compacidad
para demostrar que $\mathcal{T}$ es satisfactible.
\par 
Sea $\mathcal{T}_0$ cualquier subconjunto finito de $\mathcal{T}$ y sea 
$I=\{i_1,\dots , i_m\}$ el corres\-pondiente  subconjunto finito
de índices en $\mathbb{N}^{+}$ que son ``mencionados'' en $\mathcal{T}_0$, es decir,
el conjunto de todos los índices $i\in \mathbb{N}^{+}$ tal que $C_{i,x}$
para algún $x\in S_i$, ocurre en alguna fórmula de $\mathcal{T}_0$. 
\par

Consideremos la familia de conjuntos $\{S_{i_1},\dots , S_{i_m}\}$. Entonces, 
$\mathcal{T}_0$ está contenido en el conjunto 
$\mathcal{T}_1 = \mathcal{F}_0  \cup \mathcal{G}_0 \cup \mathcal{H}_0$ 
donde,
\begin{enumerate}
\item
$ \mathcal{F}_0 =
\left  \{\vee_{x\in S_{n}} C_{n, x}\mid n\in I \right \},$
\item
$ \mathcal{G}_0 =\{ \neg (C_{n,x}\wedge C_{n,y})\mid  x, y \in S_n, x\neq y, n \in I\},$
\item
$ \mathcal{H}_0 =\{\neg (C_{n,x}\wedge C_{m,x})\mid x\in S_n\cap S_m, n \neq m,  n, m\in I \}.$
\end{enumerate}

Por hipótesis, $\{S_{i_1},\dots , S_{i_m}\}$ cumple la condición ($M^{ * }$) y en particular la 
condición ($M$). 
Luego por el Teorema de  Hall (versión finita) existe una función $f:I\to  \bigcup_{i\in I}S_i$ 
tal que $f$ es un SRD para $\{S_{i_1},\dots , S_{i_m}\}$.
\par 
En consecuencia, un modelo para $\mathcal{T}_1$ es la interpretación 
$v: \mathcal{P} \to \{\V,\F\}$ definida por, 

$$ v(C_{n,x}) =  
\begin{cases}
                          \V, & \text{ si } n\in I\text{   y   } f(n) = x, \\
                          \F, & \text{en caso contrario.}
                         \end{cases}
$$

Es decir, se tiene que $v(F)=\V$ para toda fórmula  $F\in \mathcal{T}_1$, por ser $f$ un SRD de
$\{S_{i_1},\dots , S_{i_m}\}$.
\par 
Luego, $\mathcal{T}_1$ es satisfactible y por tanto $T_0$ es satisfactible. De esta forma,
$\mathcal{T}$ es finitamente satisfactible y por  consiguiente, por el Teorema de Compacidad,
es satisfactible.

Sea $I: \mathcal{P} \to  \{\V, \F\}$ un modelo de $\mathcal{T}$. 
Definimos la función $f:\mathbb{N}^{+} \to  \bigcup_{ n \in \mathbb{N}^{+}} S_n$ por,
  \[f(m) = x \text{ si y solamente si } I(C_{m,x})= \V. \]
Entonces, 
$f$ es un  SRD para $\{S_n\}_{n\in \mathbb{N}^{+}}:$
\par
Puesto que $\mathcal{F}$ y $\mathcal{G}$ son satisfactibles, a cada  $m\in \mathbb{N}^{+}$ 
le corresponde exactamente un elemento en  $S_m$ (es decir, $f$ es una función);
además, como  $\mathcal{H}$ es satisfactible se tiene que $f$ es inyectiva.
\<close>
section \<open>Formalización\<close>
text\<open>
La formalización de la prueba descrita en la sección anterior consta de  250 líneas 
(sin tener en cuenta lo correspondiente a la formalización del Teorema de Compacidad) que 
incluyen 7 definiciones y 43 lemas.
\par   
A continuación describimos la especificación en Isabelle de las principales definiciones y resultados
utilizados en  la demostración.
\<close>
text\<open>
Representamos la colección enumerable  de conjuntos finitos  $\{S_n\}_{n\in \mathbb{N}^{+}}$  en HOL,
de acuerdo a  \textcolor{blue}{ \cite{DBLP:conf/cpp/JiangN11}},
por medio de  una función $S\, :: \,a \Rightarrow\,\, b\,\, set$ junto con un conjunto de índices 
$I \, :: \,a\,\, set$, donde $a$ y $b$ son  tipos enumerables arbitrarios,
tal que  para todo $i\in I$, el conjunto $(S\,\, i)$ es finito. 
\par
La formalización de un SRD para $S$ e $I$ es cualquier función $R\, :: \,a \Rightarrow\,\,  b\,\, set$
que satisface el siguiente predicado.                
\<close>
system_representatives 
definition sistema_representantes :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"sistema_representantes S I R  \<equiv> (\<forall>i\<in>I. (R i) \<in> (S i)) \<and> (inj_on R I)"
text\<open>
donde $(inj \text{-}on\,R\,  I)$ significa que la función $R$ es inyectiva sobre el conjunto $I$.
\<close>
text\<open>
La condición de matrimonio para $S$ e $I$ se formaliza por la proposición, 
$$\forall J\subseteq I.\, finite\, J \longrightarrow  card\, J\leq card\,
\left ( \bigcup\, (S \text{ ' }  J)\right)$$
donde $ S \text{ ' }  J = \{S\,x\,|\, x\in J\}$.
\<close>
text\<open>
Teniendo en cuenta lo anterior, formalizamos en Isabelle el enunciado del teorema de Hall de la
siguiente manera:
\<close>
text\<open>
\textit{
\isacommand{theorem}\isamarkupfalse%
\ SRD{\isacharcolon}\isanewline
\ \ \isakeyword{fixes}\ S\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}
{\isacharprime}a\ {\isasymRightarrow}\ {\isacharprime}b\ set{\isachardoublequoteclose}
\ \isakeyword{and}\ I\ \ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}
{\isacharprime}a\ set{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{assumes}\isanewline
\ {\isachardoublequoteopen}\ {\isasymexists}g{\isachardot}
 enumeracion\ {\isacharparenleft}g{\isacharcolon}{\isacharcolon}\ nat\ {\isasymRightarrow}
{\isacharprime}a{\isacharparenright}{\isachardoublequoteclose}\ \isakeyword{and}
 {\isachardoublequoteopen}{\isasymexists}h{\isachardot}\ enumeracion
 {\isacharparenleft}h{\isacharcolon}{\isacharcolon}\ nat\ {\isasymRightarrow}
{\isacharprime}b{\isacharparenright}{\isachardoublequoteclose}\ \isanewline
\ \ \isakeyword{and}\ {\isachardoublequoteopen}{\isasymforall}i{\isasymin}I{\isachardot}
 finite\ {\isacharparenleft}S\ i{\isacharparenright}{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{and}\ {\isachardoublequoteopen}{\isasymforall}J{\isasymsubseteq}I{\isachardot}
 finite\ J\ {\isasymlongrightarrow}\ card\ J\ {\isasymle}\ card\ {\isacharparenleft}
{\isasymUnion}\ {\isacharparenleft}S\ {\isacharbackquote}\ J{\isacharparenright}
{\isacharparenright}{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{shows}\ {\isachardoublequoteopen}{\isasymexists}R{\isachardot}
 sistema{\isacharunderscore}representantes\ S\ I\ R{\isachardoublequoteclose}
}
\<close>
(*<*)set_to_list
definition conj_a_lista :: "'a set \<Rightarrow> 'a list"
  where "conj_a_lista s =  (SOME l. set l = s)"

(*fun conj_a_listaD :: "'a set \<Rightarrow> 'a list"
  where
  "conj_a_listaD S} =  []"   
|  "conj_a_listaD {a} = [a]"
| "conj_a_listaD S = (SOME l. set l = S)" *)
set_set_to_list
lemma  conj_conj_a_list:
   "finite s \<Longrightarrow> set (conj_a_lista s) = s"
  unfolding conj_a_lista_def by (metis (mono_tags) finite_list some_eq_ex)
list_set
lemma lista_conjunto:
  assumes "finite (S i)"
  shows "set (conj_a_lista (S i)) = (S i)"
  using assms conj_conj_a_list  conj_conj_a_list  by auto
(*>*)
text\<open>
Las siguientes definiciones en Isabelle  corresponden a la formalización de los conjuntos
 $\mathcal{F}, \mathcal{G}, \mathcal{H}$ y $\mathcal{T}$ respectivamente.
\<close>
disjunction_atomic
primrec disyuncion_atomicas :: "'b list \<Rightarrow>'a \<Rightarrow> ('a \<times> 'b)formula"  where
 "disyuncion_atomicas [] i = FF"   
| "disyuncion_atomicas (x#D) i = (Atomo (i, x)) \<or>. (disyuncion_atomicas D i)"

definition \<F> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> (('a \<times> 'b)formula) set"  where
   "\<F> S I  \<equiv> (\<Union>i\<in>I. { disyuncion_atomicas (conj_a_lista (S i)) i })"
atom
definition \<G> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b)formula set"  where
   " \<G> S I \<equiv> {\<not>.(Atomo (i,x) \<and>. Atomo(i,y))
                         |x y i . x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I}"

definition \<H> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow>('a \<times> 'b)formula set"  where
   "\<H> S I \<equiv> {\<not>.(Atomo (i,x) \<and>. Atomo(j,x))
                         | x i j. x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)}"

definition \<T> :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b)formula set"  where
   "\<T> S I  \<equiv> (\<F> S I) \<union> (\<G> S I) \<union> (\<H> S I)" 

text\<open>
Definimos en Isabelle el conjunto de índices que ocurren en un conjunto de fórmulas de la siguiente 
manera.
\<close>  
primrec indices_formula :: "('a \<times> 'b)formula  \<Rightarrow> 'a set" where
  "indices_formula FF = {}"
| "indices_formula TT = {}"
| "indices_formula (Atomo P) =  {fst P}"
| "indices_formula (\<not>. F) = indices_formula F"
| "indices_formula (F \<and>. G) = indices_formula F \<union> indices_formula G"
| "indices_formula (F \<or>. G) = indices_formula F \<union> indices_formula G"
| "indices_formula (F \<rightarrow>. G) = indices_formula F \<union> indices_formula G"
indices_set_formulas
definition  indices_conjunto_formulas :: "('a \<times> 'b)formula set  \<Rightarrow> 'a set" where
"indices_conjunto_formulas S = (\<Union>F\<in> S. indices_formula F)"
(*<*)
 finite_indices_formulas
lemma finito_indices_formula:
  shows "finite (indices_formula F)"
  by(induct F, auto)
 finite_set_indices
lemma finito_conjunto_indices:
  assumes  "finite S"
  shows "finite (indices_conjunto_formulas S)" 
 using `finite S` finito_indices_formula 
  by(unfold indices_conjunto_formulas_def, auto)

indices_disjunction
lemma indices_disyuncion:
  assumes "F = disyuncion_atomicas L  i" and "L \<noteq> []"
  shows "indices_formula F = {i}" 
proof-
  have  "(F = disyuncion_atomicas L  i  \<and>  L \<noteq> []) \<Longrightarrow> indices_formula F = {i}"
  proof(induct L arbitrary: F)
    case Nil hence False using assms by auto
    thus ?case by auto
  next
    case(Cons a L)
    assume "F = disyuncion_atomicas (a # L) i \<and> a # L \<noteq> []" 
    thus ?case
    proof(cases L)
      assume "L = []"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
      thus "indices_formula F = {i}" using Cons(2) by auto
    next
      show
  "\<And>b list. F = disyuncion_atomicas (a # L) i \<and> a # L \<noteq> [] \<Longrightarrow> L = b # list \<Longrightarrow> 
            indices_formula F = {i}" 
        using Cons(1-2) by auto
    qed
  qed 
  thus ?thesis using assms  by auto
qed    

nonempty_set_list
lemma no_vacia:
  assumes "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)"     
  shows "\<forall>i\<in>I. conj_a_lista (S i)\<noteq>[]"  
proof(rule ccontr)
  assume "\<not> (\<forall>i\<in>I. conj_a_lista (S i) \<noteq> [])" 
  hence "\<exists>i\<in>I. conj_a_lista (S i) = []" by auto 
  hence "\<exists>i\<in>I. set(conj_a_lista (S i)) = {}" by auto
  then obtain i where i: "i\<in>I" and  "set (conj_a_lista (S i)) = {}" by auto
  thus False using lista_conjunto[of S i]  assms by auto
qed

at_least_subset_indices
lemma  indices_algun:
  assumes "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)"  
  shows  "indices_conjunto_formulas (\<F> S I) \<subseteq> I" 
proof
  fix i
  assume hip: "i \<in> indices_conjunto_formulas (\<F> S I)" show  "i \<in> I"
  proof-  
    have "i \<in> (\<Union>F\<in>(\<F> S I). indices_formula F)" using hip
      by(unfold indices_conjunto_formulas_def,auto)
    hence "\<exists>F \<in> (\<F> S I). i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<F> S I)" and i: "i \<in> indices_formula F" by auto
    hence "\<exists> k\<in>I. F = disyuncion_atomicas (conj_a_lista (S k)) k"
      by (unfold \<F>_def, auto) 
    then obtain k where
    k: "k\<in>I" and "F = disyuncion_atomicas (conj_a_lista (S k)) k" by auto
    hence "indices_formula F = {k}"
      using assms  no_vacia[of I S] 
      indices_disyuncion[OF `F = disyuncion_atomicas (conj_a_lista (S k))  k`]
      by auto
    hence "k = i" using i by auto
    thus ?thesis using k by auto
  qed
qed
at_most_subset_indices
lemma indices_maximo:
  shows "indices_conjunto_formulas (\<G> S I) \<subseteq> I"
proof
  fix i
  assume hip: "i \<in> indices_conjunto_formulas (\<G> S I)" show  "i \<in> I"
  proof-
    have "i \<in> (\<Union>F\<in>(\<G> S I). indices_formula F)" using hip
      by(unfold indices_conjunto_formulas_def,auto)
    hence "\<exists>F\<in>(\<G> S I). i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<G> S I)" and i: "i \<in> indices_formula F"
      by auto
    hence "\<exists>x y j. x\<in>(S j) \<and> y\<in>(S j) \<and> x\<noteq>y \<and> j\<in>I \<and> F = 
           \<not>.(Atomo (j, x) \<and>. Atomo(j,y))"
      by (unfold \<G>_def, auto)
    then obtain x y j where "x\<in>(S j) \<and> y\<in>(S j) \<and> x\<noteq>y \<and> j\<in>I"
      and "F = \<not>.(Atomo (j, x) \<and>. Atomo(j,y))"
      by auto
    hence "indices_formula F = {j} \<and> j\<in>I" by auto
    thus "i \<in> I" using i by auto
  qed
qed

different_subset_indices
lemma  indices_diferentes:
  shows "indices_conjunto_formulas (\<H> S I) \<subseteq> I" 
proof
  fix i
  assume hip: "i \<in> indices_conjunto_formulas (\<H> S I)" show "i \<in> I"
  proof-
    have "i \<in> (\<Union>F\<in>(\<H> S I). indices_formula F)" using hip
      by(unfold indices_conjunto_formulas_def,auto)
    hence "\<exists>F\<in>(\<H> S I) . i \<in> indices_formula F" by auto
    then obtain F where "F\<in>(\<H> S I)" and i: "i \<in> indices_formula F"
      by auto
    hence "\<exists> x j k. x \<in> (S j) \<inter> (S k) \<and> (j\<in>I \<and> k\<in>I \<and> j\<noteq>k) \<and> F =
           \<not>.(Atomo (j,x) \<and>. Atomo(k,x))"
      by (unfold \<H>_def, auto)
    then obtain x j k
      where "(j\<in>I \<and> k\<in>I \<and> j\<noteq>k) \<and> F = \<not>.(Atomo (j, x) \<and>. Atomo(k,x))"
      by auto
    hence u: "j\<in>I" and v: "k\<in>I" and "indices_formula F = {j,k}"
      by auto
    hence "i=j \<or> i=k"  using i by auto
    thus "i \<in> I" using u v  by auto
  qed
qed
indices_union_sets
lemma ii:
  shows "indices_conjunto_formulas(A \<union> B) = (indices_conjunto_formulas A) \<union> (indices_conjunto_formulas B)"
   by(unfold  indices_conjunto_formulas_def, auto)

lemma ii1:
  assumes "F\<in>(\<F> S I)"
  shows "(indices_formula F) \<subseteq> (indices_conjunto_formulas (\<F> S I))"
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_conjunto_formulas (\<F> S I)"
  proof-
    have "\<exists>F. F\<in>(\<F> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus  ?thesis by(unfold indices_conjunto_formulas_def, auto)
  qed
qed 

lemma ii2:
  assumes  "F\<in>(\<G> S I)"
  shows "(indices_formula F) \<subseteq> (indices_conjunto_formulas (\<G> S I))" 
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_conjunto_formulas (\<G> S I)"
  proof-
    have "\<exists>F. F\<in>(\<G> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_conjunto_formulas_def, auto)
  qed
qed

lemma ii3:
  assumes  "F\<in>(\<H> S I)"
  shows "(indices_formula F) \<subseteq> (indices_conjunto_formulas (\<H> S I))" 
proof
  fix i 
  assume hip: "i \<in> indices_formula F"
  show  "i \<in> indices_conjunto_formulas (\<H> S I)"
  proof-
    have "\<exists>F. F\<in>(\<H> S I) \<and> i \<in> indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_conjunto_formulas_def, auto)
  qed
qed

lemma aaa:
  assumes  "\<forall>i\<in>I.(S i)\<noteq>{}" and "\<forall>i\<in>I. finite(S i)"
  shows "indices_conjunto_formulas (\<T> S I) \<subseteq> I"
proof
  fix i
  assume hip: "i \<in> indices_conjunto_formulas (\<T> S I)" show "i \<in> I"
  proof-
    have  "i \<in> indices_conjunto_formulas ((\<F> S I) \<union> (\<G> S I)  \<union> (\<H> S I))"
      using hip by (unfold \<T>_def,auto)
    hence "i \<in> indices_conjunto_formulas ((\<F> S I) \<union> (\<G> S I)) \<union>
    indices_conjunto_formulas(\<H> S I)"
      using ii[of "(\<F> S I) \<union> (\<G> S I)"] by auto
    hence "i \<in> indices_conjunto_formulas ((\<F> S I) \<union> (\<G> S I)) \<or> 
    i \<in> indices_conjunto_formulas(\<H> S I)"
      by auto
    thus ?thesis
    proof(rule disjE)        
      assume hip: "i \<in> indices_conjunto_formulas (\<F> S I \<union> \<G> S I)"       
      hence "i \<in> (\<Union>F\<in> (\<F> S I) \<union> (\<G> S I). indices_formula F)"
        by(unfold  indices_conjunto_formulas_def, auto)
      then obtain F
      where F: "F\<in>(\<F> S I) \<union> (\<G> S I)" and i: "i \<in> indices_formula F" by auto 
      from F have  "(indices_formula F) \<subseteq> (indices_conjunto_formulas (\<F> S I))
      \<or> indices_formula F \<subseteq> (indices_conjunto_formulas (\<G> S I))"
        using ii1 ii2 by blast
      hence "i \<in> indices_conjunto_formulas (\<F> S I) \<or>
               i \<in> indices_conjunto_formulas (\<G> S I)"
        using i by auto
      thus "i \<in> I" 
        using assms indices_algun[of I S] indices_maximo[of S I] by auto
      next
      assume "i \<in> indices_conjunto_formulas (\<H> S I)" 
      hence
      "i \<in> (\<Union>F\<in>(\<H> S I). indices_formula F)" 
        by(unfold  indices_conjunto_formulas_def, auto)
      then obtain F where F:  "F\<in>(\<H> S I)" and i: "i \<in> indices_formula F"
        by auto
      from F have "(indices_formula F) \<subseteq> (indices_conjunto_formulas (\<H> S I))"
        using ii3 by blast
      hence "i \<in> indices_conjunto_formulas (\<H> S I)" using i by auto
      thus "i \<in> I" using indices_diferentes[of S I]
        by auto
    qed
  qed
qed

lemma isf:
  assumes "S \<subseteq> H" 
  shows  "indices_conjunto_formulas S \<subseteq> indices_conjunto_formulas H" 
proof
  fix i
  assume "i \<in> indices_conjunto_formulas S"
  hence "\<exists>F. F \<in> S \<and> i \<in> indices_formula F"
    by(unfold indices_conjunto_formulas_def, auto) 
  hence "\<exists>F. F \<in> H \<and> i \<in> indices_formula F" using assms by auto
  thus  "i \<in> indices_conjunto_formulas H" 
    by(unfold indices_conjunto_formulas_def, auto)
qed

lemma indices_subconjunto_formulas:
  assumes  "\<forall>i\<in>I.(S i)\<noteq>{}" and "\<forall>i\<in>I. finite(S i)" and "A \<subseteq> (\<T> S I)" 
  shows "(indices_conjunto_formulas A) \<subseteq> I" 
proof-
  have "(indices_conjunto_formulas A) \<subseteq> (indices_conjunto_formulas (\<T> S I))"
    using assms(3) isf by auto
  thus ?thesis using assms(1-2) aaa[of I S] by auto
qed

lemma contenido:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and  "To \<subseteq> (\<T> S I)"
  shows "To \<subseteq> (\<T> S (indices_conjunto_formulas To))"
proof
  fix F
  assume hip: "F \<in> To" 
  hence "F \<in> (\<T> S I)" using assms(3) by auto
  hence "F \<in> (\<F> S I) \<union> (\<G> S I) \<union> (\<H> S I)" by(unfold \<T>_def,auto)
  hence "F \<in> (\<F> S I) \<or> F \<in> (\<G> S I) \<or> F \<in> (\<H> S I)" by auto
  thus "F\<in>(\<T> S (indices_conjunto_formulas To))"  
  proof(rule disjE)
    assume "F \<in> (\<F> S I)"
    hence "\<exists>i\<in>I. F =  disyuncion_atomicas (conj_a_lista (S i)) i" 
      by(unfold \<F>_def,auto)
    then obtain i
      where i: "i\<in>I" and F: "F =  disyuncion_atomicas (conj_a_lista (S i)) i"
      by auto
    hence "indices_formula F = {i}"
      using 
      assms(1-2) no_vacia[of I S] indices_disyuncion[of F "(conj_a_lista (S i))" i ]
      by auto
    hence "i\<in>(indices_conjunto_formulas To)" using hip
      by(unfold indices_conjunto_formulas_def,auto)
    hence "F\<in>(\<F> S (indices_conjunto_formulas To))" 
      using F by(unfold \<F>_def,auto)
    thus "F\<in>(\<T> S (indices_conjunto_formulas To))"
      by(unfold \<T>_def,auto)
  next
    assume "F \<in> (\<G> S I) \<or> F \<in> (\<H> S I)"
    thus ?thesis
    proof(rule disjE)
      assume "F \<in> (\<G> S I)" 
      hence "\<exists>x.\<exists>y.\<exists>i. F = \<not>.(Atomo (i,x) \<and>. Atomo(i,y)) \<and> x\<in>(S i) \<and>
               y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
        by(unfold \<G>_def, auto)
      then obtain x y i
        where F1: "F = \<not>.(Atomo (i,x) \<and>. Atomo(i,y))" and
                F2: "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
        by auto
      hence "indices_formula F = {i}" by auto
      hence "i\<in>(indices_conjunto_formulas To)" using hip
        by(unfold indices_conjunto_formulas_def,auto)
      hence "F\<in>(\<G> S (indices_conjunto_formulas To))"
        using F1 F2 by(unfold \<G>_def,auto)
      thus "F\<in>(\<T> S (indices_conjunto_formulas To))"  by(unfold \<T>_def,auto)
    next
      assume "F \<in> (\<H> S I)"
      hence "\<exists>x.\<exists>i.\<exists>j. F = \<not>.(Atomo (i,x) \<and>. Atomo(j,x)) \<and> 
              x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)" 
        by(unfold  \<H>_def, auto)
      then obtain x i j
        where F3: "F = \<not>.(Atomo (i,x) \<and>. Atomo(j,x))" and 
                F4: " x \<in> (S i) \<inter> (S j) \<and> (i\<in>I \<and> j\<in>I \<and> i\<noteq>j)" 
        by auto 
      hence "indices_formula F = {i,j}" by auto
      hence "i\<in>(indices_conjunto_formulas To) \<and> j\<in>(indices_conjunto_formulas To)" 
        using hip by(unfold indices_conjunto_formulas_def,auto)
      hence "F\<in>(\<H> S (indices_conjunto_formulas To))"
        using F3 F4 by(unfold \<H>_def,auto)
      thus "F\<in>(\<T> S (indices_conjunto_formulas To))"  by(unfold \<T>_def,auto)
    qed
  qed
qed

lemma conjuntos_no_vacios:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "A \<subseteq> (\<T> S I)" 
  shows   "\<forall>i\<in>(indices_conjunto_formulas A). (S i)\<noteq>{}"
proof-
  have "(indices_conjunto_formulas A)\<subseteq>I" 
    using assms(1-3) indices_subconjunto_formulas[of I S A] by auto
  thus ?thesis using assms(1) by auto
qed

lemma conjuntos_finitos:
  assumes  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "A \<subseteq> (\<T> S I)" 
shows  "\<forall>i\<in>(indices_conjunto_formulas A). finite (S i)"
proof-
  have  "(indices_conjunto_formulas A)\<subseteq>I" 
    using assms(1-3) indices_subconjunto_formulas[of I S A] by auto
  thus  "\<forall>i\<in>(indices_conjunto_formulas A). finite (S i)" using assms(2) by auto
qed

lemma conjuntos_no_vacios1:
  assumes  "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
  shows "\<forall>i\<in>I. (S i)\<noteq>{}" using assms by auto
(*>*)
text\<open>
El siguiente lema afirma que  para cualquier
subconjunto finito de fórmulas $To\subseteq  (\mathcal{T}\, S\, I)$,
si la correspondiente colección de subconjuntos finitos con índices en el conjunto
$(indices\text{-}conjunto\text{-}formulas\,\, To)$  sa\-tisface la condición de
matrimonio, entonces tiene un SRD.
Para la demostración se utiliza la versión finita del teorema de Hall
\textcolor{blue}{ \cite{DBLP:conf/cpp/JiangN11}}.
\<close>
lemma sistema_representates_finito:
  assumes
  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "To \<subseteq> (\<T> S I)"  and "finite To" 
   and "\<forall>J\<subseteq>(indices_conjunto_formulas To). card J \<le> card (\<Union> (S ` J))"
 shows  "\<exists>R. sistema_representantes S (indices_conjunto_formulas To) R" 
(*<*)
proof- 
  have 1: "finite (indices_conjunto_formulas To)"
    using assms(4) finito_conjunto_indices by auto
  have  "\<forall>i\<in>(indices_conjunto_formulas To). finite (S i)"
    using conjuntos_finitos assms(1-3) by auto
  hence  "\<exists>R. (\<forall>i\<in>(indices_conjunto_formulas To). R i \<in> S i) \<and> 
              inj_on R (indices_conjunto_formulas To)" 
    using 1 assms(5) marriage_HV[of "(indices_conjunto_formulas To)" S] by auto
  then obtain R 
    where R: "(\<forall>i\<in>(indices_conjunto_formulas To). R i \<in> S i) \<and> 
              inj_on R (indices_conjunto_formulas To)" by auto 
  thus ?thesis by(unfold sistema_representantes_def, auto)
qed
(*>*)
text\<open>
El siguiente teorema afirma que si se tiene un sistema de representantes distintos $R$ para una colección
de conjuntos finitos determinada por $A$ e $\mathcal{I}$, entonces cualquier subconjunto de fórmulas 
 $X\subseteq (\mathcal{T}\, A\,\, \mathcal{I})$ es satisfactible.
Un modelo para $X$ es la  siguiente interpretación de fórmulas.
\<close>
fun interpretacion_hall :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a \<times> 'b) \<Rightarrow> v_verdad)"  where
"interpretacion_hall A \<I> R = (\<lambda>(i,x).(if  i \<in> \<I> \<and> x \<in> (A i) \<and> (R i) = x  then Verdad else Falso))"

(*<*)
lemma valor_indice:
  assumes  "valor (interpretacion_hall S I R) (Atomo (i,x)) = Verdad"
  shows  "(R i) = x"
proof(rule ccontr)
  assume  "(R i) \<noteq> x" hence "valor (interpretacion_hall S I R) (Atomo (i,x)) \<noteq> Verdad" 
    by auto
  hence "valor (interpretacion_hall S I R) (Atomo (i,x)) = Falso" 
  using no_verdad[of "interpretacion_hall S I R" "Atomo (i,x)"] by auto 
  thus False using assms by simp
qed

lemma valor2:
  assumes "F = \<not>.(Atomo (i,x) \<and>. Atomo(i,y))" and "x\<noteq>y"  
  shows "valor (interpretacion_hall S I R) F = Verdad"
proof(rule ccontr)
  assume "valor (interpretacion_hall S I R) F \<noteq> Verdad"
  hence
  "valor (interpretacion_hall S I R) (\<not>.(Atomo (i,x) \<and>. Atomo (i, y))) \<noteq> Verdad" 
    using assms(1) by auto
  hence
  "valor (interpretacion_hall S I R) (\<not>.(Atomo (i,x) \<and>. Atomo (i, y))) = Falso"
    using
  no_verdad[of "interpretacion_hall S I R" "\<not>.(Atomo (i,x) \<and>. Atomo (i, y))"]
    by auto     
  hence  "valor (interpretacion_hall S I R) ((Atomo (i,x) \<and>. Atomo (i, y))) = Verdad" 
    using
  ValoresNegacion1[of "interpretacion_hall S I R" "(Atomo (i,x) \<and>. Atomo (i, y))"]
    by auto
  hence "valor (interpretacion_hall S I R) (Atomo (i,x)) = Verdad" and
  "valor (interpretacion_hall S I R) (Atomo (i, y)) = Verdad"
    using
 ValoresConjuncion[of "interpretacion_hall S I R" "Atomo (i,x)" "Atomo (i, y)"]
    by auto
  hence "(R i)= x" and "(R i)= y" using valor_indice by auto
  hence "x=y" by auto
  thus False using assms(2) by auto
qed

lemma valor3:
  assumes
  "F = \<not>.(Atomo (i,x) \<and>. Atomo(j,x))"  and "i\<in>I \<and> j\<in>I" and "i\<noteq>j" and "inj_on R I"
  shows "valor (interpretacion_hall S I R) F = Verdad"
proof(rule ccontr)
  assume "valor (interpretacion_hall S I R) F \<noteq> Verdad"
  hence  "valor (interpretacion_hall S I R) (\<not>.(Atomo (i,x) \<and>. Atomo (j,x))) \<noteq> Verdad"
    using assms(1) by auto
  hence
  "valor (interpretacion_hall S I R) (\<not>.(Atomo (i,x) \<and>. Atomo (j, x))) = Falso" using
  no_verdad[of "interpretacion_hall S I R" "\<not>.(Atomo (i,x) \<and>. Atomo (j, x))" ]
    by auto
  hence  "valor (interpretacion_hall S I R) ((Atomo (i,x) \<and>. Atomo (j, x))) = Verdad" 
    using 
 ValoresNegacion1[of "interpretacion_hall S I R" "(Atomo (i,x) \<and>. Atomo (j, x))"] 
    by auto
  hence "valor (interpretacion_hall S I R) (Atomo (i,x)) = Verdad" and
  "valor (interpretacion_hall S I R) (Atomo (j, x)) = Verdad"
    using ValoresConjuncion[of "interpretacion_hall S I R" "Atomo (i,x)" "Atomo (j,x)"]
    by auto
  hence  "(R i)= x"  and  "(R j)= x" using valor_indice by auto
  hence "(R i) = (R j)" by auto
  hence "i=j" using  `i\<in>I \<and> j\<in>I` `inj_on R I` by(unfold inj_on_def, auto)
  thus False using  `i\<noteq>j`  by auto
qed

lemma valor_verdad_disyuncion_atomicas:
  assumes "x \<in> set l" and "valor I (Atomo (i,x)) = Verdad"
  shows "valor I (disyuncion_atomicas l i) = Verdad"
proof-
  have "x \<in> set l \<Longrightarrow> valor I (Atomo (i,x)) = Verdad \<Longrightarrow>
  valor I (disyuncion_atomicas l i) = Verdad" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show  "valor I (disyuncion_atomicas (a # l) i) = Verdad"
    proof-
      have "x = a \<or> x\<noteq>a" by auto
      thus  "valor I (disyuncion_atomicas (a # l) i) = Verdad"
      proof(rule disjE)
        assume "x = a"
          hence
          1:"(disyuncion_atomicas (a#l) i) = 
             (Atomo (i,x)) \<or>. (disyuncion_atomicas l i)"
          by auto 
        have "valor I ((Atomo (i,x)) \<or>. (disyuncion_atomicas l i)) = Verdad"  
          using Cons(3)  by(unfold valor_def,unfold v_disyuncion_def, auto)
        thus ?thesis using 1  by auto
      next
        assume "x \<noteq> a"
        hence "x\<in> set l" using Cons(2) by auto
        hence "valor I (disyuncion_atomicas l i ) = Verdad"
          using Cons(1) Cons(3) by auto
        thus ?thesis
          by(unfold valor_def,unfold v_disyuncion_def, auto)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma valor_verdad_disyuncion_formulas:
  assumes  "finite (S i)"
  and  "x \<in> (S i)  \<and>  valor I (Atomo (i,x)) = Verdad" 
  and  "F = disyuncion_atomicas (conj_a_lista (S i)) i " 
  shows "valor I F = Verdad"
proof- 
  have "set (conj_a_lista (S i)) = (S i)" 
  using  conj_conj_a_list assms(1) by auto
  hence "x \<in> set (conj_a_lista (S i))"
    using assms(2) by auto
  thus "valor I F = Verdad"
    using assms(2-3) valor_verdad_disyuncion_atomicas by auto
qed
(*>*)

theorem SRD_satisfactible:
  assumes "\<forall>i\<in>\<I>. (A i) \<noteq> {}"  and  "\<forall>i\<in>\<I>. finite (A i)" and  "X \<subseteq> (\<T> A \<I>)"
  and  "sistema_representantes A \<I> R"  
shows "satisfacible X"
(*<*)
proof- 
  have "satisfacible (\<T> A \<I>)"
  proof-
    have "inj_on R \<I>" using assms(4) sistema_representantes_def[of A \<I> R] by auto
    have "(interpretacion_hall A \<I> R) modelo (\<T> A \<I>)"
    proof(unfold modelo_def) 
      show "\<forall>F \<in> (\<T> A \<I>). valor (interpretacion_hall A \<I> R) F = Verdad"
      proof 
        fix F assume "F \<in> (\<T> A \<I>)"
        show  "valor (interpretacion_hall A \<I> R) F  = Verdad"
        proof-
          have "F \<in> (\<F> A \<I>) \<union> (\<G> A \<I>) \<union> (\<H> A \<I>)" 
            using  `F \<in> (\<T> A \<I>)` assms(3)  by(unfold \<T>_def,auto) 
          hence  "F \<in> (\<F> A \<I>) \<or> F \<in> (\<G> A \<I>) \<or> F \<in> (\<H> A \<I>)" by auto  
          thus ?thesis
          proof(rule disjE) 
            assume "F \<in> (\<F> A \<I>)"
            hence "\<exists>i\<in>\<I>. F =  disyuncion_atomicas (conj_a_lista (A i)) i" 
              by(unfold \<F>_def,auto)
            then obtain i
              where i: "i\<in>\<I>" and F: "F =  disyuncion_atomicas (conj_a_lista (A i)) i"
              by auto
            have 1: "finite (A i)" using i  assms(2) by auto
            have 2: " i \<in> \<I> \<and> (R i) \<in> (A i)" 
              using i assms(4) by (unfold sistema_representantes_def, auto)
            hence "valor (interpretacion_hall A \<I> R) (Atomo (i,(R i))) = Verdad"
              by auto 
            thus "valor (interpretacion_hall A \<I> R) F  = Verdad"
              using 1 2 assms(4) F           
            valor_verdad_disyuncion_formulas
            [of A i "(R i)" "(interpretacion_hall A \<I> R)" F]
              by auto
          next
            assume "F \<in> (\<G> A \<I>) \<or> F \<in> (\<H> A \<I>)"
            thus ?thesis
            proof(rule disjE)
              assume "F \<in> (\<G> A \<I>)"
              hence
            "\<exists>x.\<exists>y.\<exists>i. F = \<not>.(Atomo (i,x) \<and>. Atomo(i,y)) \<and> x\<in>(A i) \<and>
              y\<in>(A i) \<and>  x\<noteq>y \<and> i\<in>\<I>"
                by(unfold \<G>_def, auto)
              then obtain x y i
                where F: "F = \<not>.(Atomo (i,x) \<and>. Atomo(i,y))" 
            and "x\<in>(A i) \<and> y\<in>(A i) \<and>  x\<noteq>y \<and> i\<in>\<I>"
                by auto
          thus "valor (interpretacion_hall A \<I> R) F  = Verdad"
            using `inj_on R \<I>` valor2[of F i x y A \<I> R] by auto
          next
              assume "F \<in> (\<H> A \<I>)"
              hence "\<exists>x.\<exists>i.\<exists>j. F = \<not>.(Atomo (i,x) \<and>. Atomo(j,x)) \<and>
                   x \<in> (A i) \<inter> (A j) \<and> (i\<in>\<I> \<and> j\<in>\<I> \<and> i\<noteq>j)" 
                 by(unfold  \<H>_def, auto)
              then obtain x i j
              where "F = \<not>.(Atomo (i,x) \<and>. Atomo(j,x))"  and "(i\<in>\<I> \<and> j\<in>\<I> \<and> i\<noteq>j)" 
                 by auto
              thus "valor (interpretacion_hall A \<I> R) F  = Verdad" using `inj_on R \<I>`
              valor3[of F i x j \<I> ]  by auto             
            qed
          qed
        qed
      qed
    qed
    thus "satisfacible (\<T> A \<I>)" by(unfold satisfacible_def, auto)
  qed 
  thus "satisfacible X" using Subconjunto_satisfacible assms(3) by auto
qed 
(*>*)
text\<open>
Los anteriores dos resultados permiten demostrar que cualquier
subconjunto finito de fórmulas  $To\subseteq  (\mathcal{T}\, S\, I)$  tal que
la correspondiente colección de subconjuntos finitos cumplen la condición de matrimonio, es satisfactible.  
\<close>
lemma satisfactible_finito:
  assumes
  "\<forall>i\<in>I. (S i)\<noteq>{}" and "\<forall>i\<in>I. finite (S i)" and "To \<subseteq> (\<T> S I)"  and  "finite To"
  and "\<forall>J\<subseteq>(indices_conjunto_formulas To). card J \<le> card (\<Union> (S ` J))"
shows  "satisfacible To"
(*<*)
proof- 
  have 0: "\<exists>R. sistema_representantes S (indices_conjunto_formulas To) R" 
    using assms sistema_representates_finito[of I S To] by auto
  then obtain R
    where R: "sistema_representantes S (indices_conjunto_formulas To) R" by auto
  have 1: "\<forall>i\<in>(indices_conjunto_formulas To). (S i)\<noteq>{}" 
    using assms(1-3) conjuntos_no_vacios  by blast
  have 2: "\<forall>i\<in>(indices_conjunto_formulas To). finite (S i)" 
    using assms(1-3) conjuntos_finitos by blast
  have 3: "To\<subseteq>(\<T> S (indices_conjunto_formulas To))"
    using assms(1-3) contenido[of I S To] by auto 
  thus  "satisfacible To"
    using  1 2 3 0 SRD_satisfactible by auto
qed
(*>*)
text\<open>
El anterior lemma junto con el Teorema de Compacidad permiten demostrar que el conjunto de fórmulas
$(\mathcal{T}\, S\, I)$ es satisfactible.
\<close>
(*<*)
lemma diag_nat:
  shows "\<forall>y z.\<exists>x. (y,z) = diag x" 
  using enumeracion_natxnat by(unfold enumeracion_def,auto)

lemma EnumFormulasHall:
  assumes "\<exists>g. enumeracion (g:: nat \<Rightarrow>'a)" and "\<exists>h. enumeracion (h:: nat \<Rightarrow>'b)"
  shows "\<exists>f. enumeracion (f:: nat \<Rightarrow>('a \<times>'b )formula)"
proof-
  from assms(1) obtain g where e1: "enumeracion (g:: nat \<Rightarrow>'a)" by auto  
  from assms(2) obtain h where e2: "enumeracion (h:: nat \<Rightarrow>'b)" by auto  
  have "enumeracion ((\<lambda>m.(g(fst(diag m)),(h(snd(diag m))))):: nat \<Rightarrow>('a \<times>'b))"
  proof(unfold enumeracion_def) 
    show  "\<forall>y::('a \<times> 'b). \<exists>m. y = (g (fst (diag m)), h (snd (diag m)))"  
    proof
      fix y::"('a \<times>'b )" 
      show "\<exists>m. y = (g (fst (diag m)), h (snd (diag m)))"
      proof-
        have  "y = ((fst y), (snd y))" by auto
        from e1 have  "\<forall>w::'a. \<exists>n1. w = (g n1)" by(unfold enumeracion_def, auto)
        hence "\<exists>n1. (fst y) = (g n1)" by auto
        then obtain n1 where n1: "(fst y) = (g n1)" by auto 
        from e2 have  "\<forall>w::'b. \<exists>n2. w = (h n2)" by(unfold enumeracion_def, auto)
        hence "\<exists>n2. (snd y) = (h n2)" by auto
        then obtain n2 where n2: "(snd y) = (h n2)" by auto
        have "\<exists>m. (n1, n2) = diag m" using diag_nat by auto
        hence "\<exists>m. (n1, n2) = (fst (diag m), snd (diag m))" by simp
        hence "\<exists>m.((fst y), (snd y)) = (g(fst (diag m)), h(snd (diag m)))"
          using n1 n2 by blast
        thus "\<exists>m. y = (g (fst (diag m)), h(snd (diag m)))" by auto
      qed
    qed
  qed
  thus "\<exists>f. enumeracion (f:: nat \<Rightarrow>('a \<times>'b )formula)" 
    using EnumeracionFormulasP1 by auto 
qed
(*>*)
theorem satisfacible_T:
  fixes S :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "\<exists>g. enumeracion (g:: nat \<Rightarrow>'a)" and "\<exists>h. enumeracion (h:: nat \<Rightarrow>'b)" 
  and "\<forall>i\<in>I. finite (S i)"
  and "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
shows "satisfacible (\<T> S I)"
(*<*)
proof- 
  have "\<forall> A. A \<subseteq> (\<T> S I) \<and> (finite A) \<longrightarrow> satisfacible A"
  proof(rule allI, rule impI) 
    fix A assume "A \<subseteq> (\<T> S I) \<and> (finite A)"
    hence hip1:  "A \<subseteq> (\<T> S I)" and  hip2: "finite A" by auto
    show "satisfacible A"
    proof -
      have 0: "\<forall>i\<in>I. (S i)\<noteq>{}" using assms(4) conjuntos_no_vacios1 by auto
      hence 1: "(indices_conjunto_formulas A)\<subseteq>I"  
        using assms(3) hip1 indices_subconjunto_formulas[of I S A] by auto
      have 2: "finite (indices_conjunto_formulas A)" 
        using hip2 finito_conjunto_indices by auto
      have 3: "card (indices_conjunto_formulas A) \<le>
                 card(\<Union> (S ` (indices_conjunto_formulas A)))"
        using 1 2 assms(4) by auto
      have "\<forall>J\<subseteq>(indices_conjunto_formulas A). card J \<le> card(\<Union> (S ` J))"
     proof(rule allI)
       fix J
       show "J \<subseteq> indices_conjunto_formulas A \<longrightarrow> card J \<le> card (\<Union> (S ` J)) "
       proof(rule impI)
         assume hip: "J\<subseteq>(indices_conjunto_formulas A)"              
       hence 4: "finite J" 
         using 2  rev_finite_subset by auto 
       have "J\<subseteq>I" using hip 1 by auto
       thus "card J \<le> card (\<Union> (S ` J))" using 4  assms(4) by auto      
     qed
   qed
   thus "satisfacible A"
     using 0 assms(3) hip1 hip2 satisfactible_finito[of I S A]  by auto
 qed
qed
  thus "satisfacible (\<T> S I)" using 
  TeoremaCompacidad1[OF  EnumFormulasHall[OF
  `\<exists>g. enumeracion (g:: nat \<Rightarrow>'a)`  `\<exists>h. enumeracion (h:: nat \<Rightarrow>'b)` ],
       of "(\<T> S I)"]
    by auto
qed
(*>*)
text\<open>
El siguiente teorema afirma que si $(\mathcal{T}\,  S\, I)$ es satisfactible
 entonces la co\-rrespondiente colección
de conjuntos finitos  determinada por $S$ e $I$ tiene un sistema de representantes distintos.
\<close>
text\<open> Para la demostración se define la siguiente función, 
\<close>
fun SRD ::  "(('a \<times> 'b) \<Rightarrow> v_verdad) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow>'b )"
  where
"SRD M S I = (\<lambda>i. (THE x. (valor M (Atomo (i,x)) = Verdad) \<and> x\<in>(S i)))"
text\<open> y se demuestra el siguiente lema que formaliza la existencia de tal función.
\<close>
(*<*)
lemma valor_disyuncion_lista1:
  assumes "valor I (disyuncion_atomicas (a # l) i) = Verdad"
  shows "valor I (Atomo (i,a)) = Verdad \<or> valor I (disyuncion_atomicas l i) = Verdad" 
proof-
  have
  "(disyuncion_atomicas (a # l) i) = (Atomo (i,a)) \<or>. (disyuncion_atomicas l i)"
    by auto
  hence "valor I ((Atomo (i ,a)) \<or>. (disyuncion_atomicas l i)) = Verdad" 
    using assms by auto
  thus ?thesis using ValoresDisyuncion by blast
qed

lemma valor_atomo:
  assumes "valor I (disyuncion_atomicas l i) = Verdad"
  shows "\<exists>x. x \<in> set l \<and> (valor I (Atomo (i,x)) = Verdad)"
proof-
  have "valor I (disyuncion_atomicas l i) = Verdad \<Longrightarrow>
  \<exists>x. x \<in> set l \<and> (valor I (Atomo (i,x)) = Verdad)"
  proof(induct l)
    case Nil
    then show ?case by auto
  next   
    case (Cons a l)  
    show  "\<exists>x. x \<in> set (a # l) \<and> valor I (Atomo (i,x)) = Verdad"  
    proof-
      have
      "(valor I (Atomo (i,a)) = Verdad) \<or> valor I (disyuncion_atomicas l i)=Verdad" 
        using Cons(2) valor_disyuncion_lista1[of I] by auto      
      thus ?thesis
    proof(rule disjE)
      assume "valor I (Atomo (i,a)) = Verdad"
      thus ?thesis by auto
    next
      assume "valor I (disyuncion_atomicas l i) = Verdad" 
      thus ?thesis using Cons by auto    
    qed
  qed
qed
  thus ?thesis using assms by auto
qed 

lemma funcion_existencia_SRD:
 assumes "i \<in> I" and "M modelo (\<F> S I)" and "finite(S i)"  
  shows "\<exists>x. (valor M (Atomo (i,x)) = Verdad) \<and>  x \<in> (S i)" 
proof- 
  from  `i \<in> I`  
  have  "(disyuncion_atomicas (conj_a_lista (S i)) i) \<in> (\<F> S I)" 
    by(unfold \<F>_def,auto)
  hence "valor M (disyuncion_atomicas(conj_a_lista (S i)) i) = Verdad"
    using assms(2) modelo_def[of M "\<F> S I"] by auto
  hence 1: "\<exists>x. x \<in> set (conj_a_lista (S i)) \<and> (valor M (Atomo (i,x)) = Verdad)"
    using valor_atomo[of M "(conj_a_lista (S i))" i] by auto
  thus  "\<exists>x. (valor M (Atomo (i,x)) = Verdad) \<and>  x \<in> (S i)" 
    using   `finite(S i)` conj_conj_a_list[of "(S i)"] by auto
qed

lemma solo_un_conjunto_elem:
  shows  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow>
          (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))\<in> (\<G> S I))"
proof(rule allI) 
  fix y
  show "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I \<longrightarrow> 
       (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))\<in> (\<G> S I))"
  proof(rule impI)
    assume "x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I"
    thus  "\<not>.(Atomo (i,x) \<and>. Atomo(i,y)) \<in> (\<G> S I)"
   by(unfold \<G>_def, auto)
  qed
qed

lemma funcion_unicidad_SRD:
 assumes "i \<in> I" and "M modelo (\<G> S I)" 
  shows  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)"
proof-
  have   "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))\<in> (\<G> S I))"
    using solo_un_conjunto_elem[of x S i] by auto
  thus  "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)"
    using assms(2)  modelo_def[of M "\<G> S I"] by blast
qed

lemma existencia:
  assumes "valor M (Atomo (i,x)) = Verdad \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y  \<longrightarrow>  valor M (Atomo (i, y)) = Falso"  
shows "\<forall>z. valor M (Atomo (i, z)) = Verdad \<and> z\<in>(S i) \<longrightarrow> z = x"
proof(rule allI)
  fix z 
  show "valor M (Atomo (i, z)) = Verdad \<and> z \<in> S i  \<longrightarrow> z = x" 
  proof(rule impI)
    assume hip: "valor M (Atomo (i, z)) = Verdad \<and> z \<in> (S i)"  
    show "z = x"
    proof(rule ccontr)
      assume 1: "z \<noteq> x"
      have   2: "z \<in> (S i)" using hip by auto
      hence  "valor M (Atomo(i,z)) =  Falso" using 1 assms(2) by auto
      thus False using hip by auto
    qed
  qed
qed

lemma unicidad:
  assumes "valor M (Atomo (i,x)) = Verdad \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)"
  shows "\<forall>y. y \<in> (S i)  \<and> x\<noteq>y  \<longrightarrow>  valor M (Atomo (i, y)) = Falso"
proof(rule allI, rule impI)
  fix y
  assume hip: "y \<in> S i \<and> x \<noteq> y"
  show "valor M (Atomo (i, y)) = Falso"
  proof(rule ccontr)
    assume "valor M (Atomo (i, y)) \<noteq> Falso" 
    hence "valor M (Atomo (i, y)) = Verdad" using CasosValor by blast
    hence 1: "valor M (Atomo (i,x) \<and>. Atomo(i,y))  = Verdad"
      using assms(1) v_conjuncion_def by auto
    have "valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad"
      using hip assms(2) by auto
    hence "valor M (Atomo (i,x) \<and>. Atomo(i,y)) = Falso" 
      using ValoresNegacion2  by blast
    thus False using 1  by auto
  qed      
qed

lemma exist_unicidad1:
  assumes  "valor M (Atomo (i,x)) = Verdad \<and> x\<in>(S i)"
  and  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)"
shows "\<forall>z. valor M (Atomo (i, z)) = Verdad \<and> z\<in>(S i) \<longrightarrow> z = x" 
  using assms  unicidad[of M i x ]  existencia[of M i x] by blast 

lemma exist_unicidad2:
  assumes "valor M (Atomo (i,x)) = Verdad \<and> x\<in>(S i)" and
  "(\<And>z.(valor M (Atomo (i, z)) = Verdad \<and> z\<in>(S i))  \<Longrightarrow> z = x)"
shows "(THE a. (valor M (Atomo (i,a)) = Verdad) \<and> a\<in>(S i)) = x" 
  using assms by(rule the_equality)

lemma exist_unicidad:
  assumes  "valor M (Atomo (i,x)) = Verdad \<and> x\<in>(S i)" and
  "\<forall>y. y \<in> (S i) \<and> x\<noteq>y \<longrightarrow> (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)"
shows  "(THE a. (valor M (Atomo (i,a)) = Verdad) \<and> a\<in>(S i)) = x" 
  using assms  exist_unicidad1[of M i x ] exist_unicidad2[of M i x] by blast
(*>*)
lemma funcion_SRD:
  assumes "i \<in> I" and "M modelo (\<F> S I)" and "M modelo (\<G> S I)" and "finite(S i)"
shows "\<exists>!x. (valor M (Atomo (i,x)) = Verdad) \<and>  x \<in> (S i) \<and> SRD M S I i = x" 
(*<*)
proof- 
  have  "\<exists>x. (valor M (Atomo (i,x)) = Verdad) \<and>  x \<in> (S i)" 
    using assms(1-2,4) funcion_existencia_SRD by auto 
  then obtain x where x: "(valor M (Atomo (i,x)) = Verdad) \<and>  x \<in> (S i)"
    by auto
  moreover
  have "\<forall>y.(x\<in>(S i) \<and> y\<in>(S i) \<and>  x\<noteq>y \<and> i\<in>I) \<longrightarrow> 
  (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(i,y))) = Verdad)" 
    using assms(1,3) funcion_unicidad_SRD[of i I M S]  by auto
  hence "(THE a. (valor M (Atomo (i,a)) = Verdad) \<and> a\<in>(S i)) = x"
   using x  `i \<in> I`  exist_unicidad[of M i x] by auto 
  hence "SRD M S I i = x"  by auto
  hence "(valor M (Atomo (i,x)) = Verdad \<and> x \<in> (S i)) \<and> SRD M S I i = x"
    using x by auto
  thus ?thesis  by auto
qed

lemma \<H>1:
  assumes
  "(valor M (Atomo (i,a)) = Verdad) \<and> a \<in> (S i)"
  and "(valor M (Atomo (j,b)) = Verdad) \<and> b \<in> (S j)" 
  and  "i\<in>I \<and> j\<in>I \<and> i\<noteq>j" 
  and "(a \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j \<longrightarrow>
  (valor M (\<not>.(Atomo (i,a) \<and>. Atomo(j,a))) = Verdad))"
  shows  "a \<noteq> b"
proof(rule ccontr)
  assume  "\<not> a \<noteq> b" 
  hence hip: "a=b" by auto
  hence "valor M (Atomo (i, a)) = Verdad" and  "valor M (Atomo (j, a)) = Verdad"
    using assms by auto
  hence "valor M (Atomo (i, a) \<and>. Atomo(j,a)) = Verdad" using v_conjuncion_def
    by auto
  hence "valor M (\<not>.(Atomo (i, a) \<and>. Atomo(j,a))) = Falso" 
    using v_negacion_def by auto
  moreover
  have  "a \<in> (S i) \<inter> (S j)" using hip assms(1-2) by auto
  hence "valor M (\<not>.(Atomo (i, a) \<and>. Atomo(j, a))) = Verdad" 
    using assms(3-4) by auto
  ultimately show False by auto
qed

lemma modelo_conjuntos:
  assumes  "M modelo (\<T> S I)"
  shows  "M modelo (\<F> S I)" and  "M modelo (\<G> S I)" and  "M modelo (\<H> S I)" 
proof(unfold modelo_def)
  show "\<forall>F\<in>\<F> S I. valor M F = Verdad"
  proof
    fix F
    assume "F\<in> (\<F> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
next
  show "\<forall>F\<in>(\<G> S I). valor M F = Verdad"
  proof
    fix F
    assume "F\<in>(\<G> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
next
  show "\<forall>F\<in>(\<H> S I). valor M F = Verdad"
  proof
    fix F
    assume "F\<in>(\<H> S I)" hence "F\<in>(\<T> S I)" by(unfold \<T>_def, auto) 
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
qed
(*>*)
text\<open>
\<close>
(*<*)
lemma conjuntos_distintos:
  assumes
  hip1: "i\<in>I" and  hip2: "j\<in>I" and  hip3: "i\<noteq>j" and  hip4: "M modelo (\<T> S I)"
  and hip5: "finite(S i)" and  hip6: "finite(S j)"
shows "SRD M S I i  \<noteq>  SRD M S I j" 
proof-
  have 1: "M modelo \<F> S I" and 2:  "M modelo \<G> S I"
    using hip4 modelo_conjuntos by auto
  hence "\<exists>!x. (valor M (Atomo (i,x)) = Verdad) \<and> x \<in> (S i) \<and> SRD M S I i = x"
    using  hip1  hip4  hip5 funcion_SRD[of i I M S] by auto  
  then obtain x where
  x1: "(valor M (Atomo (i,x)) = Verdad) \<and> x \<in> (S i)" and x2: "SRD M S I i = x"
    by auto 
  have "\<exists>!y. (valor M (Atomo (j,y)) = Verdad) \<and> y \<in> (S j) \<and> SRD M S I j = y"
  using 1 2  hip2  hip4  hip6 funcion_SRD[of j I M S] by auto   
  then obtain y where
  y1: "(valor M (Atomo (j,y)) = Verdad) \<and> y \<in> (S j)" and y2: "SRD M S I j = y"
    by auto
  have "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (\<not>.(Atomo (i,x) \<and>. Atomo(j,x))\<in> (\<H> S I))"
    by(unfold  \<H>_def, auto)
  hence "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (\<not>.(Atomo (i,x) \<and>. Atomo(j,x)) \<in> (\<T> S I))"
    by(unfold  \<T>_def, auto)
  hence "(x \<in> (S i) \<inter> (S j) \<and> i\<in>I \<and> j\<in>I \<and> i\<noteq>j) \<longrightarrow>
  (valor M (\<not>.(Atomo (i,x) \<and>. Atomo(j,x))) = Verdad)" 
    using hip4 modelo_def[of M "\<T> S I"] by auto
  hence "x \<noteq> y" using x1 y1 assms(1-3) \<H>1[of M i x  S  j y I] 
    by auto
  thus ?thesis using x2 y2 by auto
qed  
(*>*)
text\<open>
\<close>
theorem satisfactible_representante:
  assumes "satisfacible (\<T> S I)" and "\<forall>i\<in>I. finite (S i)"
  shows "\<exists>R. sistema_representantes S I R"
(*<*)
proof-
  from assms have "\<exists>M. M modelo (\<T> S I)"  by(unfold satisfacible_def)
  then obtain M where M: "M modelo (\<T> S I)" by auto 
  hence  "sistema_representantes S I (SRD M S I)" 
  proof(unfold sistema_representantes_def) 
    show "(\<forall>i\<in>I. (SRD M S I i) \<in> (S i)) \<and> inj_on (SRD M S I) I" 
    proof(rule conjI)
      show "\<forall>i\<in>I. (SRD M S I i) \<in> (S i)"
      proof 
        fix i
        assume i: "i \<in> I"
        have "M modelo \<F> S I" and 2: "M modelo \<G> S I" using M modelo_conjuntos
          by auto
        thus "(SRD M S I i) \<in> (S i)"
          using i M assms(2) modelo_conjuntos[of M S I]
                  funcion_SRD[of i I M S ] by auto 
      qed
    next
      show "inj_on (SRD M S I) I"
      proof(unfold  inj_on_def)
        show "\<forall>i\<in>I. \<forall>j\<in>I. SRD M S I i = SRD M S I j \<longrightarrow> i = j"
        proof 
          fix i 
          assume 1:  "i \<in> I"
          show "\<forall>j\<in>I. SRD M S I i = SRD M S I j \<longrightarrow> i = j"
          proof 
            fix j
            assume 2:  "j \<in> I"
            show "SRD M S I i = SRD M S I j \<longrightarrow> i = j"
            proof(rule ccontr)
              assume  "\<not> (SRD M S I i = SRD M S I j \<longrightarrow> i = j)"
              hence 5:  "SRD M S I i = SRD M S I j" and 6:  "i\<noteq> j" by auto
              have  3: "finite(S i)" and 4: "finite(S j)" using 1 2  assms(2) by auto
              have "SRD M S I i \<noteq> SRD M S I j"
                using 1 2 3 4 6 M conjuntos_distintos[of i I j M S] by auto
              thus False  using 5 by auto
            qed
          qed 
        qed
      qed
    qed
  qed
  thus  "\<exists>R. sistema_representantes S I R" by auto
qed
(*>*)
text\<open>
Por último tenemos la formalización del teorema de Hall.
\<close>
theorem Hall:
  fixes S :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "\<exists>g. enumeracion (g:: nat \<Rightarrow>'a)" and "\<exists>h. enumeracion (h:: nat \<Rightarrow>'b)" 
  and Finitos: "\<forall>i\<in>I. finite (S i)"
  and Matrimonio: "\<forall>J\<subseteq>I. finite J \<longrightarrow>  card J \<le> card (\<Union> (S ` J))"
 shows "\<exists>R. sistema_representantes S I R"
proof-  
  have "satisfacible (\<T> S I)" using assms satisfacible_T[of I] by auto
  thus ?thesis using Finitos Matrimonio satisfactible_representante[of S I] by auto
qed

(*<*)
end
(*>*)
