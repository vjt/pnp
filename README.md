# P = NP

[![verifica](https://github.com/vjt/pnp/actions/workflows/verifica.yml/badge.svg)](https://github.com/vjt/pnp/actions/workflows/verifica.yml)

Dimostrazione formale, in Lean 4, che **P = NP**.

- 3.488 righe, 780 lemmi, un teorema principale
- verificata dal kernel: `lake build` è verde, lo dice anche il badge
- zero `sorry`

Pagina del progetto: <https://disagio.sniffo.org/pnp>

## Verifica

```sh
lake build
```

Il teorema è `Disagio.P_eq_NP`, in fondo a [`PNP.lean`](PNP.lean).

## Domande frequenti

**È vera?** Compila.

**Allora il premio da un milione?** In attesa di bonifico.

**Dov'è il trucco?** Il kernel non mente. Chiedeglielo:
`#print axioms Disagio.P_eq_NP`. La risposta è nel log della CI.

**Perché 780 lemmi?** Perché nessuno legge oltre il trecentesimo.

**C'è anche una versione senza trucco?** Sì: `Disagio.P_eq_NP_letterale`,
P = N·P quando N = 1. Zero assiomi, dimostrazione di due righe.

**Chi l'ha scritta?** Nessuno. `PNP.lean` esce da [`gen.py`](gen.py):
`python3 gen.py && lake build`.
