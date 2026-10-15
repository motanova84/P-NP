# Formalización de Máquinas de Turing en Lean 4

Este documento describe la implementación completa de Máquinas de Turing deterministas en Lean 4, siguiendo las definiciones estándar de la teoría de la computación.

## Estructura del Código

### 1. Definiciones Básicas

#### TapeAlphabet
```lean
class TapeAlphabet (Γ : Type*) extends Fintype Γ where
  blank : Γ
```
Define un alfabeto finito para la cinta con un símbolo en blanco distinguido.

#### InputAlphabet
```lean
class InputAlphabet (Σ Γ : Type*) extends TapeAlphabet Γ where
  input_subset : Σ → Γ
  no_blank : ∀ σ : Σ, input_subset σ ≠ blank
```
Define un alfabeto de entrada como subconjunto del alfabeto de cinta, excluyendo el símbolo en blanco.

#### Direction
```lean
inductive Direction
  | left
  | right
  | stay
```
Las tres posibles direcciones de movimiento del cabezal de lectura/escritura.

#### TapeConfig
```lean
structure TapeConfig (Γ : Type*) where
  left : List Γ
  current : Γ
  right : List Γ
```
Representa la configuración de la cinta:
- `left`: contenido a la izquierda del cabezal (en orden reverso)
- `current`: símbolo bajo el cabezal
- `right`: contenido a la derecha del cabezal

Operaciones disponibles:
- `moveLeft`: mueve el cabezal a la izquierda
- `moveRight`: mueve el cabezal a la derecha
- `write`: escribe un símbolo en la posición actual
- `move`: mueve según una dirección dada

### 2. Máquina de Turing Determinista

#### StateSet
```lean
class StateSet (Q : Type*) extends Fintype Q where
  start : Q
  accept : Q
  reject : Q
  start_neq_accept : start ≠ accept
  start_neq_reject : start ≠ reject
  accept_neq_reject : accept ≠ reject
```
Define el conjunto finito de estados con estados especiales:
- `start`: estado inicial
- `accept`: estado de aceptación
- `reject`: estado de rechazo

#### TuringMachine
```lean
structure TuringMachine (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  δ : Q → Γ → Option (Q × Γ × Direction)
  halt_no_transition : ∀ γ : Γ,
    δ StateSet.accept γ = none ∧
    δ StateSet.reject γ = none
```
Define una máquina de Turing con:
- `δ`: función de transición (Q × Γ → Q × Γ × Direction)
- `halt_no_transition`: garantiza que los estados de aceptación y rechazo no tienen transiciones

#### Config
```lean
structure Config (Σ Γ Q : Type*) 
  [InputAlphabet Σ Γ] [StateSet Q] where
  state : Q
  tape : TapeConfig Γ
```
Configuración completa de la máquina (estado + cinta).

### 3. Semántica de Ejecución

#### step
```lean
def step (c : Config Σ Γ Q) : Option (Config Σ Γ Q)
```
Ejecuta un paso de computación según la función de transición.

#### run
```lean
def run (c : Config Σ Γ Q) : ℕ → Option (Config Σ Γ Q)
```
Ejecuta `n` pasos de computación desde una configuración.

#### initialConfig
```lean
def initialConfig (input : List Σ) : Config Σ Γ Q
```
Crea la configuración inicial desde un input, colocando el cabezal al inicio de la cinta.

### 4. Predicados de Aceptación y Detención

#### accepts
```lean
def accepts (input : List Σ) : Prop :=
  ∃ t : ℕ, ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    c.state = StateSet.accept
```
La máquina acepta si alcanza el estado de aceptación.

#### rejects
```lean
def rejects (input : List Σ) : Prop :=
  ∃ t : ℕ, ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    c.state = StateSet.reject
```
La máquina rechaza si alcanza el estado de rechazo.

#### haltsIn
```lean
def haltsIn (input : List Σ) (t : ℕ) : Prop :=
  ∃ c : Config Σ Γ Q,
    M.run (M.initialConfig input) t = some c ∧
    (c.state = StateSet.accept ∨ c.state = StateSet.reject) ∧
    M.step c = none
```
La máquina se detiene en exactamente `t` pasos.

#### halts
```lean
def halts (input : List Σ) : Prop :=
  ∃ t : ℕ, M.haltsIn input t
```
La máquina se detiene eventualmente.

#### runTime
```lean
noncomputable def runTime (input : List Σ) : ℕ :=
  if h : M.halts input then
    Nat.find h
  else
    0
```
Devuelve el tiempo mínimo de ejecución (0 si no se detiene).

### 5. Lenguajes y Decisión

#### Language
```lean
def Language (Σ : Type*) := List Σ → Prop
```
Un lenguaje es un conjunto de strings (predicado sobre listas).

#### Decides
```lean
def Decides (M : TuringMachine Σ Γ Q) (L : Language Σ) : Prop :=
  ∀ w : List Σ, 
    (L w ↔ M.accepts w) ∧ 
    (¬L w ↔ M.rejects w) ∧
    M.halts w
```
Una máquina decide un lenguaje si:
- Acepta exactamente las palabras del lenguaje
- Rechaza exactamente las palabras fuera del lenguaje
- Se detiene para todas las entradas

#### DecidesInTime
```lean
def DecidesInTime (M : TuringMachine Σ Γ Q) (L : Language Σ) (f : ℕ → ℕ) : Prop :=
  Decides M L ∧
  ∀ w : List Σ, M.runTime w ≤ f w.length
```
Una máquina decide un lenguaje en tiempo `f(n)` donde `n` es la longitud de la entrada.

### 6. Propiedades Básicas Demostradas

#### halt_or_loop
```lean
theorem halt_or_loop (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.halts w ∨ ¬M.halts w
```
Principio del tercero excluido: una máquina o se detiene o no se detiene.

#### accepts_implies_halts
```lean
theorem accepts_implies_halts (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.accepts w → M.halts w
```
Si una máquina acepta, entonces se detiene.

#### rejects_implies_halts
```lean
theorem rejects_implies_halts (M : TuringMachine Σ Γ Q) (w : List Σ) :
  M.rejects w → M.halts w
```
Si una máquina rechaza, entonces se detiene.

#### decides_implies_total
```lean
theorem decides_implies_total (M : TuringMachine Σ Γ Q) (L : Language Σ) :
  Decides M L → ∀ w : List Σ, M.halts w
```
Si una máquina decide un lenguaje, se detiene para todas las entradas.

## Características de la Implementación

### Ventajas

1. **Estándar**: Sigue las definiciones estándar de Sipser y Arora-Barak
2. **Sin axiomas adicionales**: Solo usa Mathlib estándar (Fintype, List, Nat, Function)
3. **Tipo-segura**: Aprovecha el sistema de tipos de Lean
4. **Compositional**: Las configuraciones y operaciones están bien estructuradas
5. **Demostraciones completas**: Los teoremas básicos están completamente demostrados

### Estructura de la Cinta

La cinta se representa como tres componentes:
- Lista a la izquierda (en orden reverso para eficiencia)
- Símbolo actual bajo el cabezal
- Lista a la derecha

Esta representación permite:
- Movimientos eficientes del cabezal
- Extensión automática de la cinta (agregando blancos cuando es necesario)
- Implementación natural de las operaciones

### Función de Transición

La función de transición `δ : Q → Γ → Option (Q × Γ × Direction)` devuelve:
- `none` si la máquina está en un estado halting
- `some (q', γ', d)` con el nuevo estado, símbolo a escribir, y dirección de movimiento

## Referencias

- Michael Sipser, "Introduction to the Theory of Computation" (3rd ed, 2013)
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach" (2009)

## Uso

Ver `tests/TuringMachineTests.lean` para ejemplos de uso con alfabetos binarios y estados simples.

## Integración con el Proyecto P≠NP

Esta formalización de Máquinas de Turing proporciona la base teórica para:
1. Definir clases de complejidad (P, NP, etc.)
2. Formalizar reducciones entre problemas
3. Demostrar propiedades de complejidad computacional
4. Conectar con la teoría de grafos y treewidth para la separación P≠NP
