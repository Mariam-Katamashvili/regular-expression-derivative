# Fuzzifying Derivatives of Regular Expressions

This repository contains a paper and Rocq formalization about derivatives of regular expressions, derivative-based automata construction, and the extension of these ideas to fuzzy similarity relations.

The central idea is the following: ordinary Brzozowski derivatives describe how a regular expression changes after consuming an input symbol or word. This gives a direct way to construct deterministic finite automata, where each state is a derivative of the original expression. The paper extends this picture toward a fuzzy setting, where symbols are not matched only by exact equality but also by a similarity relation and a fixed cut value.

The repository has two main parts:

- `tex/` — the mathematical paper.
- `coq/` — the Rocq formalization of the main definitions, constructions, and proofs from the paper.

## Paper overview

The paper develops the theory in the following order.

1. **Basic definitions**

   The paper defines alphabets, words, languages, regular expressions, semantic interpretation, nullability, canonical forms, and semantic equivalence.

2. **Classical derivatives**

   It defines semantic derivatives of languages, syntactic derivatives of regular expressions, proves the semantic-syntactic correspondence theorem, and states regularity and finiteness results.

3. **Derivative automata**

   It constructs a deterministic finite automaton from a regular expression using derivatives. The states are canonical representatives of derivative expressions.

4. **Fuzzy proximity and similarity**

   It introduces fuzzy relations, proximity relations, similarity relations, similarity on words, similarity on languages, and syntactic similarity on restricted regular expressions.

5. **Fuzzy derivatives**

   It defines fuzzy derivatives of languages and regular expressions using a similarity relation and a cut value. It also relates fuzzy derivatives to ordinary derivatives over a quotient alphabet.

## Paper-to-Rocq map

The following table maps the main definitions, lemmas, propositions, and theorems from the paper to their Rocq locations.

### Section 2: Basic Definitions

| Paper item | Rocq formalization |
|---|---|
| Definition: Alphabet, words, and languages | Alphabet: `coq/src/Alphabet.v`, module types `SYM`, `OSYM`, `FINSYM`, `OFINSYM`. Words and languages: `coq/src/Languages.v`, definitions `word`, `language`. Language operations: `coq/src/Languages.v`, definitions `void`, `eps`, `atom`, `plus`, `conc`, `star`, `prod`, `compl` |
| Definition: (Restricted) Regular Expressions | `coq/src/RegexSemantics.v`, inductive definition `regex`; definition `restricted_regex` |
| Definition: Semantic interpretation | `coq/src/RegexSemantics.v`, definition `den`; language-side definitions imported from `coq/src/Languages.v`: `void`, `eps`, `atom`, `plus`, `conc`, `star`, `prod`, `compl` |
| Definition: Nullable regular expressions | `coq/src/Nullable.v`, definitions `has_eps`, `nu`; proofs `nullable_correct`, `mem_nu` |
| Definition: Semantic equivalence | `coq/src/RegexSemantics.v`, definitions `lang_eq`, `re_equiv`, `semantic_equiv`; proofs `lang_eq_refl`, `lang_eq_sym`, `lang_eq_trans`, `re_equiv_refl`, `re_equiv_sym`, `re_equiv_trans` |
| Definition: Similarity (`~`) | `coq/src/Canonicalization.v`, definitions `nf`, `similar`; normalization definitions `mkPlus`, `mkConc`, `mkStar`, `mkAnd`, `mkNot`, `canonize`, `eq_regex` |
| Lemma: Canonicalization/Normalization | `coq/src/CanonicalizationCorrectness.v`, theorem/proof `similar_iff_nf_eq`; supporting proofs `eq_regex_sound`, `eq_regex_refl`, `eq_regex_complete` |
| Lemma: Soundness of normalization | `coq/src/CanonicalizationCorrectness.v`, theorem/proof `similar_sound`; supporting proof `canonize_correct` |

### Section 3: Fuzzy Relations and T-Similarity

| Paper item | Rocq formalization |
|---|---|
| Definition (Appendix): T-norm | `coq/src/SimilarityRelations.v`, record `tnorm`; supporting proofs `tn_mono_r`, `tn_mono2`, `tn_idem_le` |
| Definition: Fuzzy relation, cut, T-similarity, Gödelian | `coq/src/SimilarityRelations.v`, definitions `fuzzy_rel`, `cut_value`, `mu_cut`, `is_T_similarity`, `is_godelian` |
| Lemma: μ-cuts of T-similarity relations are equivalences | `coq/src/SimilarityRelations.v`, proofs `T_equivalence_idem` (item 1), `T_equivalence_godelian` (item 2) |
| Definition: T-similarity on Regular Expressions - General T-norm | `coq/src/SimilarityRelations.v`, definition `RE`; star clause via `tpow`, `InfN`; clause equations `RE_refl`, `RE_Char`, `RE_Alt`, `RE_Seq`, `RE_Star`, `RE_otherwise`; supporting proofs `RE_range`, `InfN_lower`, `InfN_greatest` |
| Lemma: positive `R^E` forces a common skeleton | `coq/src/SimilarityRelations.v`, theorem `RE_pos_skeleton`; definitions `skeleton`, `holes`, `fill`; supporting proofs `RE_pos_skel_of`, `fill_skel_of`, `size_syms_of`, `tn_pos` |
| Lemma: Finite Syntactic Similarity | `coq/src/SimilarityRelations.v`, theorem `RE_nonzero_finite`; definition `sym_seqs`; supporting proofs `sym_seqs_complete`, `In_map_mem`, `RE_pos_skel_of` |

| Paper item | Paper location | Rocq location |
|---|---|---|
| Alphabet `Σ` | `tex/sections/preliminaries.tex` | `coq/src/Alphabet.v` |
| Words `Σ*` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `word := seq A` |
| Languages `L ⊆ Σ*` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `language := pred word` |
| Empty language | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `void`; `coq/src/RegexSemantics.v`, `Empty` |
| Empty word language `{ε}` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `eps`; `coq/src/RegexSemantics.v`, `Eps` |
| Atomic language `{a}` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `atom`; `coq/src/RegexSemantics.v`, `Char` |
| Union of languages | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `plus`; `coq/src/RegexSemantics.v`, `Alt` |
| Concatenation of languages | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `conc`; `coq/src/RegexSemantics.v`, `Seq` |
| Kleene star | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `star`; `coq/src/RegexSemantics.v`, `Star` |
| Intersection | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `prod`; `coq/src/RegexSemantics.v`, `And` |
| Complement | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `compl`; `coq/src/RegexSemantics.v`, `Neg` |
| Regular-expression grammar | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, inductive type `regex` |
| Semantic interpretation `L(r)` | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, `den` |
| Semantic equivalence `r ≡ s` | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, `re_equiv`, notation `r ≈ s` |
| Nullable function `ν` | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `has_eps`, `nullable`, `nu` |
| Correctness of nullable | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `nullable_correct` |
| Membership in `ν(r)` | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `mem_nu` |
| Canonical form `[r]` | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `canonize` |
| Normalization function `nf` | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `canonize` |
| Syntactic equality after canonicalization | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `same_after_canon` |
| Soundness of normalization | `tex/sections/preliminaries.tex` | `coq/src/CanonicalizationCorrectness.v`, `canonize_correct`, `canonize_equiv` |
| Derivative of a language by a symbol `∂a(L)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang_char` |
| Derivative of a language by a word `∂u(L)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang` |
| Semantic derivative laws | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang_nil`, `dlang_cat`, `dlang_correct`, `dlang_charE` |
| Syntactic derivative by a symbol `D_a(r)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char` |
| Syntactic derivative by a word `D_u(r)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D` |
| Derivative rules for `∅`, `ε`, letters, `+`, `·`, `*`, `&`, `¬` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char` |
| Rule `D_ε(r)=r` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_nil` |
| Rule `D_{uv}(r)=D_v(D_u(r))` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_cat` |
| Single-symbol derivative correctness | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char_correct` |
| Semantic-syntactic correspondence for classical derivatives | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_correct` |
| Regularity preservation for classical derivatives | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `regular`, `derivative_regular` |
| Finiteness of classical derivative languages | `tex/sections/derivative_regex_reglanguages.tex` | todo — proved only in paper and yet to be formalized |
| Derivative DFA states `[D_u(r)]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `state`, `construct_dfa` |
| DFA transition `δ(q,a)=[D_a(q)]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `canonical_derivative`, `step` |
| Initial DFA state `[r]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `construct_dfa` |
| Accepting states via nullability | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `accepting_state`, `final_states` |
| Extension of transition to words `δ*` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `delta_star`; `coq/src/AutomataConstruction.v`, `delta_star` |
| Reached state denotes derivative language | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `delta_star_constructed_lang`, `delta_star_constructed_derivative_equiv` |
| DFA correctness theorem `L(M)=L(r)` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `dfa_correctness` |
| Executable DFA construction pseudocode | `tex/sections/automata_construction.tex` | `coq/src/AutomataConstruction.v`, `goto`, `construct_dfa` |
| Correctness of executable DFA construction | `tex/sections/automata_construction.tex` | todo |
| DFA minimality theorem | `tex/sections/automata_construction.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy relation `S × S -> [0,1]` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `simval`, `fuzzy_rel` |
| Minimum T-norm | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `smin` |
| Cut value | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `cut_value` |
| μ-cut relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `mu_cut` |
| Proximity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `is_proximity` |
| Similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `is_similarity` |
| Similarity on words `R^w` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rw` |
| `R^w` is reflexive | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rw_refl` |
| `R^w` is symmetric | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rw_sym` |
| `R^w` is transitive under minimum T-norm | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rw_trans` |
| `R^w` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rw_is_similarity` |
| Similarity on languages `R^L` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RL`, `SupL`, `InfL` |
| `R^L` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RL_is_similarity` |
| Restricted regular expressions | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `classical_regex` |
| Syntactic similarity on regex `R^e` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rr` |
| `R^e` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rr_is_similarity` |
| Syntax-to-semantics inequality `R^e(r,s) ≤ R^L(L(r),L(s))` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `syntax_semantics_inequality` |
| Bridge theorem between `R^e` and `R^L` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `Rr_RL_bridge` |fuzzy_proximity_similarity_relation.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy language derivative `∂^μ_a(L)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| μ-cut equivalence on symbols | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| μ-cut equivalence on words | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Quotient alphabet `Σ^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient map `q_μ` and word extension `q_μ*` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient language `L^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient theorem for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy derivative by a word | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Cut neighborhood `S_a^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Fuzzy expression derivative `D_a^μ(r)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Fuzzy expression derivative by a word `D_u^μ(r)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Regularity preservation for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Semantic-syntactic correspondence for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Finiteness of fuzzy derivative languages | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Finiteness of fuzzy regex derivative types | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy DFA correctness | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |

## Current formalization work

We are currently working on formalizing the remaining paper-level definitions and results, including the fuzzy-derivative constructions, quotient-language results, fuzzy semantic-syntactic correspondence, finiteness theorems, and fuzzy DFA correctness.
