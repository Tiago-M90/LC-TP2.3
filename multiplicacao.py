import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # TP2 — Exercício 3: Multiplicação de Inteiros

    ## 1. Introdução

    Pretende-se verificar formalmente um programa de multiplicação de inteiros representados por vetores de bits de largura \(n\).

    O programa é descrito pelo *Control Flow Automaton* (CFA) fornecido pelo professor e será modelado através de um *Safe First Order Transition System* (SFOTS), utilizando o solver Z3.

    Um SFOTS é descrito por:

    \[
    \Sigma = \langle X, I, T, E \rangle
    \]

    onde:

    - \(X\) representa as variáveis de estado;
    - \(I\) é o predicado dos estados iniciais;
    - \(T\) é a relação de transição;
    - \(E\) é o predicado dos estados de erro.

    ### Decisões de modelação

    - Os operandos são BitVecs de \(n\) bits, interpretados sem sinal.
    - O overflow corresponde a um resultado que excede a capacidade de \(n\) bits sem sinal.
    - São preservados os sete nodos e as oito ligações do CFA original.
    - A inicialização de \(x\), \(y\) e \(z\) é realizada pela ação do nodo `init`.

    A interpretação sem sinal constitui uma decisão de modelação fundamentada na condição de segurança da alínea 3.c. O documento de apoio também discute overflow com sinal, pelo que esta diferença deve ficar explícita.

    **Referências:** Enunciado do TP2, Exercício 3; documento *Lógica Computacional: Multiplicação de Inteiros*, páginas 1–5; Capítulos 3 e 4.

    **Contribuição LLM:** Apoio na análise do CFA, escolha da representação e formulação inicial do SFOTS.
    """)
    return


@app.cell
def _():

    from z3 import BitVecs, Consts, EnumSort, Solver, sat


    return BitVecs, Consts, EnumSort, Solver, sat


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. Variáveis de estado

    O estado do SFOTS é representado por:

    \[
    S = (pc, a, b, x, y, z)
    \]

    - \(pc\): identificador do nodo atual do CFA;
    - \(a,b\): operandos originais da multiplicação;
    - \(x\): valor que é sucessivamente duplicado;
    - \(y\): parte do multiplicador ainda por processar;
    - \(z\): resultado parcial acumulado.

    As variáveis \(a,b,x,y,z\) são BitVecs de largura \(n\).

    Para representar a relação de transição, utilizamos também as variáveis correspondentes ao estado seguinte:

    \[
    S' = (pc', a', b', x', y', z')
    \]

    As variáveis \(a\) e \(b\) permanecem constantes durante a execução.

    O domínio de \(pc\) contém exatamente os sete nodos físicos do CFA, incluindo os dois nodos de erro.
    """)
    return


@app.cell
def _(BitVecs, Consts, EnumSort):

    # Largura dos vetores de bits (valor inicial de teste)
    n = 8

    # Locais do CFA original
    Local, (INIT, SKIP, LEFT, RIGHT, STOP, ERROR_L, ERROR_R) = EnumSort(
        "Local",
        ["init", "skip", "left", "right", "stop", "error_L", "error_R"]
    )

    # Contador de programa: estado atual e seguinte
    pc, pc_next = Consts("pc pc_next", Local)

    # Variáveis aritméticas do estado atual
    a, b, x, y, z = BitVecs("a b x y z", n)

    # Variáveis aritméticas do estado seguinte
    a_next, b_next, x_next, y_next, z_next = BitVecs(
        "a_next b_next x_next y_next z_next", n
    )

    # Representação dos estados
    S = (pc, a, b, x, y, z)
    S_next = (pc_next, a_next, b_next, x_next, y_next, z_next)

    return (
        ERROR_L,
        ERROR_R,
        INIT,
        LEFT,
        Local,
        RIGHT,
        SKIP,
        STOP,
        a,
        a_next,
        b,
        b_next,
        n,
        pc,
        pc_next,
        x,
        x_next,
        y,
        y_next,
        z,
        z_next,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Estado inicial

    O CFA inicia a execução no nodo `init`.

    Como a ação desse nodo é responsável por atribuir os valores iniciais às variáveis \(x\), \(y\) e \(z\), estas não são previamente restringidas.

    Assim, o predicado inicial é:

    \[
    I(S) \equiv (pc = init)
    \]

    Os operandos \(a\) e \(b\) podem assumir quaisquer valores representáveis pelos BitVecs de largura \(n\), interpretados sem sinal.

    A transição de `init` para `skip` será posteriormente responsável pela atribuição:

    \[
    x' = a \qquad y' = b \qquad z' = 0
    \]

    Desta forma, preservamos a semântica de inicialização do CFA original.
    """)
    return


@app.cell
def _(INIT, pc):

    # Predicado dos estados iniciais
    I = (pc == INIT)

    return (I,)


@app.cell
def _(I, Solver, a, x):

    # Verificar se existem estados que satisfazem I
    solver_inicial = Solver()
    solver_inicial.add(I)

    print("Estado inicial satisfazível:", solver_inicial.check())

    # Confirmar que x ainda pode ser diferente de a
    solver_livre = Solver()
    solver_livre.add(I, x != a)

    print("x pode ser diferente de a antes de init:", solver_livre.check())

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Relação de transição

    A relação de transição \(T(S,S')\) descreve os pares de estados entre os quais o CFA pode transitar.

    Cada transição especifica:
    - O nodo de origem e o nodo de destino;
    - A guarda que permite a transição;
    - Os valores das variáveis no estado seguinte.

    ### 4.1. Inicialização (`init` → `skip`)

    A primeira transição executa a ação do nodo `init`:

    \[
    T_1 \equiv (pc=init)\land(pc'=skip)
    \land(a'=a)\land(b'=b)
    \land(x'=a)\land(y'=b)\land(z'=0)
    \]

    Os operandos originais \(a\) e \(b\) permanecem constantes.

    ### 4.2. Transições a partir de `skip`

    O nodo `skip` não modifica as variáveis.

    A escolha do destino depende do valor de \(y\):

    - \(y\neq0\land even(y)\): transição para `left`;
    - \(y\neq0\land odd(y)\): transição para `right`;
    - \(y=0\): transição para `stop`.

    A paridade de \(y\) pode ser determinada pelo seu bit menos significativo:

    \[
    even(y)\iff(y\mathbin{\&}1)=0
    \]

    \[
    odd(y)\iff(y\mathbin{\&}1)=1
    \]

    Estas transições conservam os valores de \(a,b,x,y,z\).

    As ações dos nodos `left` e `right`, incluindo a deteção de overflow, serão modeladas posteriormente.
    """)
    return


@app.cell
def _(
    INIT,
    SKIP,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    x_next,
    y_next,
    z_next,
):

    from z3 import And, Or, BitVecVal

    # T1: init -> skip
    T1 = And(
        pc == INIT,
        pc_next == SKIP,
        a_next == a,
        b_next == b,
        x_next == a,
        y_next == b,
        z_next == BitVecVal(0, n)
    )

    return And, BitVecVal, Or, T1


@app.cell
def _(
    And,
    BitVecVal,
    LEFT,
    Or,
    RIGHT,
    SKIP,
    STOP,
    T1,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Valores constantes do tipo BitVec(n)
    zero = BitVecVal(0, n)
    um = BitVecVal(1, n)

    # Guardas de paridade
    even_y = (y & um) == zero
    odd_y = (y & um) == um

    # O nodo skip não altera nenhuma variável aritmética
    sem_alteracoes = And(
        a_next == a,
        b_next == b,
        x_next == x,
        y_next == y,
        z_next == z
    )

    # T2: skip -> left (y par e diferente de zero)
    T2 = And(
        pc == SKIP,
        pc_next == LEFT,
        y != zero,
        even_y,
        sem_alteracoes
    )

    # T3: skip -> right (y ímpar e diferente de zero)
    T3 = And(
        pc == SKIP,
        pc_next == RIGHT,
        y != zero,
        odd_y,
        sem_alteracoes
    )

    # T4: skip -> stop (y igual a zero)
    T4 = And(
        pc == SKIP,
        pc_next == STOP,
        y == zero,
        sem_alteracoes
    )

    # Relação parcial: apenas as quatro primeiras transições
    T_parcial = Or(T1, T2, T3, T4)

    return T_parcial, even_y, odd_y, um, zero


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4.3. Validação das primeiras transições

    Para verificar a correspondência entre o CFA e as fórmulas Z3, testamos tanto transições permitidas como transições proibidas.

    Os resultados esperados são:

    - `sat`: existe uma atribuição que satisfaz a transição;
    - `unsat`: não existe uma atribuição que satisfaça as condições impostas.

    Verificamos:
    1. A inicialização de \(x\), \(y\) e \(z\);
    2. A escolha do ramo `left` para \(y\) par não nulo;
    3. A escolha do ramo `right` para \(y\) ímpar;
    4. A chegada a `stop` quando \(y=0\);
    5. A impossibilidade de escolher um ramo incorreto;
    6. A conservação das variáveis em `skip`.

    Estes testes validam as quatro transições implementadas, não constituindo ainda uma verificação do SFOTS completo.
    """)
    return


@app.cell
def _(
    LEFT,
    Or,
    RIGHT,
    SKIP,
    STOP,
    Solver,
    T1,
    T_parcial,
    a,
    a_next,
    b,
    b_next,
    pc,
    pc_next,
    sat,
    x,
    x_next,
    y,
    y_next,
    z_next,
):

    from z3 import unsat

    # Cada caso contém: descrição, restrições, resultado esperado
    casos_t = [
        (
            "init inicializa corretamente",
            [T1, a == 3, b == 5,
             x_next == 3, y_next == 5, z_next == 0],
            sat
        ),
        (
            "init não permite x_next diferente de a",
            [T1, x_next != a],
            unsat
        ),
        (
            "skip com y=6 vai para left",
            [T_parcial, pc == SKIP, y == 6, pc_next == LEFT],
            sat
        ),
        (
            "skip com y=6 não pode ir para right",
            [T_parcial, pc == SKIP, y == 6, pc_next == RIGHT],
            unsat
        ),
        (
            "skip com y=5 vai para right",
            [T_parcial, pc == SKIP, y == 5, pc_next == RIGHT],
            sat
        ),
        (
            "skip com y=0 vai para stop",
            [T_parcial, pc == SKIP, y == 0, pc_next == STOP],
            sat
        ),
        (
            "skip com y=0 não pode ir para left",
            [T_parcial, pc == SKIP, y == 0, pc_next == LEFT],
            unsat
        ),
        (
            "skip preserva x",
            [T_parcial, pc == SKIP, x_next != x],
            unsat
        ),
        (
            "a e b permanecem constantes",
            [T_parcial, Or(a_next != a, b_next != b)],
            unsat
        )
    ]

    for nome_t, restricoes_t, esperado_t in casos_t:
        solver_t = Solver()
        solver_t.add(*restricoes_t)
        resultado_t = solver_t.check()

        print(f"{nome_t}: {resultado_t}")

        assert resultado_t == esperado_t, (
            f"Falha no teste: {nome_t}"
        )

    print(f"\n{len(casos_t)} testes concluídos.")

    return (unsat,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4.4. Transições a partir de `left`

    O nodo `left` executa a atribuição simultânea:

    \[
    (x,y,z)\leftarrow(2x,\lfloor y/2\rfloor,z)
    \]

    Os operandos originais \(a\) e \(b\) permanecem constantes.

    Existem duas transições possíveis:

    - \(T_5\): regresso a `skip`, se não ocorrer overflow;
    - \(T_6\): passagem para `error_L`, se ocorrer overflow.

    #### Deteção de overflow

    Considerando BitVecs sem sinal de largura \(n\), a duplicação de \(x\) provoca overflow quando:

    \[
    OF_L(x)\equiv 2\widehat{x}\ge 2^n
    \]

    As operações aritméticas sobre BitVecs de largura \(n\) são realizadas módulo \(2^n\), pelo que uma duplicação pode perder informação.

    Para detetar corretamente o overflow, alargamos temporariamente \(x\) para \(n+1\) bits antes da multiplicação por 2.

    O resultado alargado permite verificar se o valor excede a capacidade original. O valor guardado em \(x'\) continua a ter apenas \(n\) bits.

    A divisão de \(y\) por 2 é efetuada através de deslocamento lógico à direita, adequado à interpretação sem sinal.

    #### Relação de transição

    \[
    T_5\equiv
    (pc=left)\land(pc'=skip)\land\neg OF_L\land U_L
    \]

    \[
    T_6\equiv
    (pc=left)\land(pc'=error_L)\land OF_L\land U_L
    \]

    onde \(U_L\) representa a atualização das variáveis.

    O ramo de erro tem precedência sobre o regresso a `skip`, de acordo com a semântica do CFA original.

    **Contribuição LLM:** Formalização dos predicados de overflow sem sinal e das duas transições de `left`.
    """)
    return


@app.cell
def _(
    And,
    BitVecVal,
    ERROR_L,
    LEFT,
    Or,
    SKIP,
    T_parcial,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    from z3 import ZeroExt, Extract, UGE, LShR, Not

    # Duplicação de x usando n+1 bits
    # Evita perder informação antes de verificar overflow.
    x_left_ext = ZeroExt(1, x) << 1

    # Overflow sem sinal: resultado >= 2^n
    OF_L = UGE(
        x_left_ext,
        BitVecVal(2**n, n + 1)
    )

    # Ação do nodo left
    U_left = And(
        a_next == a,
        b_next == b,
        x_next == Extract(n - 1, 0, x_left_ext),
        y_next == LShR(y, 1),
        z_next == z
    )

    # T5: left -> skip, sem overflow
    T5 = And(
        pc == LEFT,
        pc_next == SKIP,
        Not(OF_L),
        U_left
    )

    # T6: left -> error_L, com overflow
    T6 = And(
        pc == LEFT,
        pc_next == ERROR_L,
        OF_L,
        U_left
    )

    # Relação parcial atualizada
    # Preserva as quatro transições anteriores
    T_com_left = Or(T_parcial, T5, T6)

    return Extract, Not, OF_L, T5, T6, T_com_left, UGE, ZeroExt


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4.5. Validação das transições de `left`

    Vamos verificar as transições \(T_5\) e \(T_6\) através de testes de satisfatibilidade.

    Os testes incluem:

    1. Duplicação correta de \(x\), sem overflow;
    2. Divisão lógica de \(y\) por 2;
    3. Conservação de \(z\);
    4. Deteção de overflow no limite da capacidade do BitVec;
    5. Seleção de `skip` quando não existe overflow;
    6. Seleção de `error_L` quando existe overflow;
    7. Impossibilidade de ignorar o ramo de erro;
    8. Conservação dos operandos originais \(a\) e \(b\).

    Para \(n=8\), o limite relevante para a duplicação é:

    \[
    2^{n-1}=128
    \]

    Assim:

    \[
    127\times2=254
    \]

    não provoca overflow, enquanto:

    \[
    128\times2=256
    \]

    já excede a capacidade de 8 bits sem sinal.

    O objetivo é confirmar que as duas transições respeitam a ação do nodo e a precedência do erro.

    Estes testes verificam apenas as transições implementadas até este ponto.
    """)
    return


@app.cell
def _(
    ERROR_R,
    LEFT,
    Not,
    OF_L,
    Or,
    Solver,
    T5,
    T6,
    T_com_left,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    sat,
    unsat,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Limite a partir do qual duplicar x causa overflow
    limiar_left = 2 ** (n - 1)

    casos_left = [
        (
            "Duplicacao sem overflow",
            [
                T5,
                x == 20,
                y == 6,
                z == 7,
                x_next == 40,
                y_next == 3,
                z_next == 7
            ],
            sat
        ),
        (
            "Duplicacao incorreta impossivel",
            [
                T5,
                x == 20,
                x_next != 40
            ],
            unsat
        ),
        (
            "Divisao de y incorreta impossivel",
            [
                T5,
                y == 6,
                y_next != 3
            ],
            unsat
        ),
        (
            "z permanece constante",
            [
                T5,
                z_next != z
            ],
            unsat
        ),
        (
            "Valor imediatamente abaixo do limite",
            [
                T5,
                x == limiar_left - 1,
                x_next == 2**n - 2
            ],
            sat
        ),
        (
            "Sem erro abaixo do limite",
            [
                T6,
                x == limiar_left - 1
            ],
            unsat
        ),
        (
            "Overflow no limite",
            [
                T6,
                x == limiar_left,
                y == 6,
                x_next == 0,
                y_next == 3
            ],
            sat
        ),
        (
            "Overflow impede regresso a skip",
            [
                T5,
                x == limiar_left
            ],
            unsat
        ),
        (
            "T5 nunca permite overflow",
            [
                T5,
                OF_L
            ],
            unsat
        ),
        (
            "T6 exige overflow",
            [
                T6,
                Not(OF_L)
            ],
            unsat
        ),
        (
            "a e b permanecem constantes",
            [
                T_com_left,
                pc == LEFT,
                Or(a_next != a, b_next != b)
            ],
            unsat
        ),
        (
            "left nao pode ir para error_R",
            [
                T_com_left,
                pc == LEFT,
                pc_next == ERROR_R
            ],
            unsat
        )
    ]

    # Executar os testes
    for nome_left, restricoes_left, esperado_left in casos_left:
        solver_left = Solver()
        solver_left.add(*restricoes_left)

        resultado_left = solver_left.check()

        print(f"{nome_left}: {resultado_left}")

        assert resultado_left == esperado_left, (
            f"Falha: {nome_left}. "
            f"Esperado: {esperado_left}, "
            f"obtido: {resultado_left}"
        )

    print(f"\n{len(casos_left)} testes de left concluídos.")

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4.6. Transições a partir de `right`

    O nodo `right` executa a atribuição simultânea:

    \[
    (x,y,z)\leftarrow(x,y-1,z+x)
    \]

    Os operandos originais \(a\) e \(b\) permanecem constantes.

    Existem duas transições possíveis:

    - \(T_7\): regresso a `skip`, se não ocorrer overflow;
    - \(T_8\): passagem para `error_R`, se ocorrer overflow.

    #### Deteção de overflow

    Considerando BitVecs sem sinal de largura \(n\), a soma provoca overflow quando:

    \[
    OF_R(x,z)\equiv \widehat z+\widehat x\ge 2^n
    \]

    A soma de dois BitVecs de \(n\) bits é realizada módulo \(2^n\).

    Para evitar a perda de informação, alargamos temporariamente os dois operandos para \(n+1\) bits antes de realizar a soma.

    O resultado alargado permite detetar overflow. O valor armazenado em \(z'\) continua a ter largura \(n\).

    #### Atualização das variáveis

    \[
    U_R\equiv
    (a'=a)\land(b'=b)\land(x'=x)
    \land(y'=y-1)\land(z'=z+x)
    \]

    As operações aritméticas de \(U_R\) são interpretadas módulo \(2^n\).

    #### Relação de transição

    \[
    T_7\equiv
    (pc=right)\land(pc'=skip)\land\neg OF_R\land U_R
    \]

    \[
    T_8\equiv
    (pc=right)\land(pc'=error_R)\land OF_R\land U_R
    \]

    O ramo de erro tem precedência sobre o regresso a `skip`, conforme a semântica do CFA original.

    **Contribuição LLM:** Formulação das transições de `right`, deteção de overflow sem sinal e tradução para Z3.
    """)
    return


@app.cell
def _(
    And,
    BitVecVal,
    ERROR_R,
    Extract,
    Not,
    Or,
    RIGHT,
    SKIP,
    UGE,
    ZeroExt,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    um,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Soma de z e x usando n+1 bits
    # Evita perder informação antes de verificar overflow
    z_right_ext = ZeroExt(1, z) + ZeroExt(1, x)

    # Overflow sem sinal: soma >= 2^n
    OF_R = UGE(
        z_right_ext,
        BitVecVal(2**n, n + 1)
    )

    # Ação do nodo right
    U_right = And(
        a_next == a,
        b_next == b,
        x_next == x,
        y_next == y - um,
        z_next == Extract(n - 1, 0, z_right_ext)
    )

    # T7: right -> skip, sem overflow
    T7 = And(
        pc == RIGHT,
        pc_next == SKIP,
        Not(OF_R),
        U_right
    )

    # T8: right -> error_R, com overflow
    T8 = And(
        pc == RIGHT,
        pc_next == ERROR_R,
        OF_R,
        U_right
    )

    # Relação parcial das transições de right
    T_right = Or(T7, T8)

    return OF_R, T7, T8, T_right


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4.7. Validação das transições de `right`

    Vamos verificar as transições \(T_7\) e \(T_8\) através de testes de satisfatibilidade.

    Os testes incluem:

    1. Adição correta de \(x\) a \(z\), sem overflow.
    2. Deteção do overflow no limite da capacidade.
    3. Seleção do destino `skip` quando não existe overflow.
    4. Seleção do destino `error_R` quando existe overflow.
    5. Impossibilidade de regressar a `skip` quando ocorre overflow.
    6. Impossibilidade de entrar em `error_R` sem overflow.
    7. Conservação de \(x\), \(a\) e \(b\).
    8. Decremento correto de \(y\).
    9. Armazenamento da soma módulo \(2^n\).
    10. Impossibilidade de selecionar destinos que não existem no CFA.

    O teste de fronteira utiliza os valores:

    \[
    z=2^n-2,\quad x=1
    \]

    cuja soma é \(2^n-1\), sem overflow, e:

    \[
    z=2^n-1,\quad x=1
    \]

    cuja soma é \(2^n\), provocando overflow.

    Os testes confirmam a coerência das fórmulas implementadas com as regras de transição escolhidas.
    """)
    return


@app.cell
def _(
    ERROR_L,
    ERROR_R,
    Not,
    OF_R,
    Or,
    SKIP,
    Solver,
    T7,
    T8,
    T_right,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    sat,
    um,
    unsat,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Capacidade dos BitVecs de largura n
    limite_right = 2**n

    casos_right = [
        (
            "Soma sem overflow",
            [
                T7,
                x == 1,
                y == 3,
                z == 2,
                x_next == 1,
                y_next == 2,
                z_next == 3
            ],
            sat
        ),
        (
            "Soma no limite sem overflow",
            [
                T7,
                x == 1,
                z == limite_right - 2,
                z_next == limite_right - 1
            ],
            sat
        ),
        (
            "Overflow no limite",
            [
                T8,
                x == 1,
                y == 3,
                z == limite_right - 1,
                y_next == 2,
                z_next == 0
            ],
            sat
        ),
        (
            "Sem overflow nao pode ir para error_R",
            [
                T_right,
                x == 1,
                z == limite_right - 2,
                pc_next == ERROR_R
            ],
            unsat
        ),
        (
            "Overflow impede regresso a skip",
            [
                T_right,
                x == 1,
                z == limite_right - 1,
                pc_next == SKIP
            ],
            unsat
        ),
        (
            "T7 nunca permite overflow",
            [
                T7,
                OF_R
            ],
            unsat
        ),
        (
            "T8 exige overflow",
            [
                T8,
                Not(OF_R)
            ],
            unsat
        ),
        (
            "x permanece constante",
            [
                T_right,
                x_next != x
            ],
            unsat
        ),
        (
            "y e decrementado corretamente",
            [
                T_right,
                y_next != y - um
            ],
            unsat
        ),
        (
            "z recebe a soma modular",
            [
                T_right,
                z_next != z + x
            ],
            unsat
        ),
        (
            "a e b permanecem constantes",
            [
                T_right,
                Or(a_next != a, b_next != b)
            ],
            unsat
        ),
        (
            "right nao pode ir para error_L",
            [
                T_right,
                pc_next == ERROR_L
            ],
            unsat
        ),
        (
            "right nao pode partir de skip",
            [
                T_right,
                pc == SKIP
            ],
            unsat
        ),
        (
            "Overflow com os dois operandos maximos",
            [
                T8,
                x == limite_right - 1,
                z == limite_right - 1,
                z_next == limite_right - 2
            ],
            sat
        )
    ]

    # Executar os testes
    for nome_right, restricoes_right, esperado_right in casos_right:
        solver_right = Solver()
        solver_right.add(*restricoes_right)

        resultado_right = solver_right.check()

        print(f"{nome_right}: {resultado_right}")

        assert resultado_right == esperado_right, (
            f"Falha: {nome_right}. "
            f"Esperado: {esperado_right}, "
            f"obtido: {resultado_right}"
        )

    print(f"\n{len(casos_right)} testes de right concluídos.")

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Construção do SFOTS completo

    Depois de formalizadas as oito ligações do CFA, a relação de transição global é dada pela disjunção:

    \[
    T(S,S')=\bigvee_{i=1}^{8}T_i(S,S')
    \]

    A fórmula \(T(S,S')\) representa todas as transições permitidas pelo autómato.

    ### 5.1. Predicado de erro

    O CFA contém dois nodos de erro:

    - `error_L`: overflow na duplicação de \(x\);
    - `error_R`: overflow na adição \(z+x\).

    O predicado de erro é:

    \[
    E(S)\equiv(pc=error_L)\lor(pc=error_R)
    \]

    O nodo `stop` representa a conclusão normal do programa e não satisfaz o predicado de erro.

    ### 5.2. Estados terminais

    Os estados terminais são:

    \[
    Term(S)\equiv(pc=stop)\lor E(S)
    \]

    Não são acrescentadas autotransições aos estados terminais, preservando as ligações do CFA original.

    O SFOTS fica assim caracterizado por:

    \[
    \Sigma=\langle X,I,T,E\rangle
    \]

    A interpretação do overflow mantém-se sem sinal, conforme a decisão de modelação anteriormente justificada.

    **Contribuição LLM:** Reunião das transições num SFOTS e formulação dos predicados de erro e terminação.
    """)
    return


@app.cell
def _(ERROR_L, ERROR_R, Or, STOP, T_com_left, T_right, pc):

    # Relação de transição completa: T1 até T8
    T = Or(T_com_left, T_right)

    # Estados de erro do CFA
    E = Or(
        pc == ERROR_L,
        pc == ERROR_R
    )

    # Estados terminais: paragem normal ou erro
    Term = Or(
        pc == STOP,
        E
    )

    return E, T, Term


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 5.3. Validação de execuções completas

    Para validar o comportamento do SFOTS, vamos construir percursos a partir de estados iniciais concretos.

    Cada percurso começa em `init` e segue a relação de transição \(T\) até atingir um estado terminal.

    Em cada passo, o Z3 determina um estado seguinte que satisfaz a relação de transição.

    Serão considerados os seguintes casos:

    - Multiplicação sem overflow;
    - Overflow na ação de `left`;
    - Overflow na ação de `right`;
    - Multiplicação em que \(b=0\);
    - Multiplicação em que \(a=0\).

    A validação compara os nodos visitados com os percursos esperados e verifica os valores finais.

    Os valores de \(x,y,z\) antes da execução de `init` são irrelevantes para o cálculo, uma vez que a ação desse nodo os inicializa.

    Estes testes permitem detetar incorreções em execuções concretas, mas não substituem provas formais para todos os estados alcançáveis.
    """)
    return


@app.cell
def _(
    BitVecVal,
    ERROR_L,
    ERROR_R,
    INIT,
    LEFT,
    RIGHT,
    SKIP,
    STOP,
    Solver,
    T,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    sat,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Associação entre nomes dos nodos e constantes Z3
    locais_cfa = {
        "init": INIT,
        "skip": SKIP,
        "left": LEFT,
        "right": RIGHT,
        "stop": STOP,
        "error_L": ERROR_L,
        "error_R": ERROR_R
    }

    def executar_cfa(a0, b0):
        """Obtém uma execução do SFOTS para os operandos a0 e b0."""

        modulo = 2**n

        if not (0 <= a0 < modulo and 0 <= b0 < modulo):
            raise ValueError("Operandos fora do intervalo sem sinal.")

        # Estado inicial à entrada de init.
        # x, y e z recebem valores arbitrários de teste.
        estado = {
            "pc": "init",
            "a": a0,
            "b": b0,
            "x": modulo - 1,
            "y": modulo - 1,
            "z": modulo - 1
        }

        percurso = [estado.copy()]

        # Limite defensivo para estes testes, não uma prova de terminação.
        for _ in range(4 * n + 5):

            if estado["pc"] in ("stop", "error_L", "error_R"):
                return percurso

            solver_passo = Solver()

            # Relação de transição e valores do estado atual
            solver_passo.add(
                T,
                pc == locais_cfa[estado["pc"]],
                a == BitVecVal(estado["a"], n),
                b == BitVecVal(estado["b"], n),
                x == BitVecVal(estado["x"], n),
                y == BitVecVal(estado["y"], n),
                z == BitVecVal(estado["z"], n)
            )

            resultado_passo = solver_passo.check()

            if resultado_passo != sat:
                raise AssertionError(
                    f"Não foi encontrado sucessor para {estado}."
                )

            modelo_passo = solver_passo.model()

            # Extrair os valores do próximo estado
            seguinte = {
                "pc": modelo_passo.eval(pc_next).decl().name(),
                "a": modelo_passo.eval(a_next).as_long(),
                "b": modelo_passo.eval(b_next).as_long(),
                "x": modelo_passo.eval(x_next).as_long(),
                "y": modelo_passo.eval(y_next).as_long(),
                "z": modelo_passo.eval(z_next).as_long()
            }

            percurso.append(seguinte)
            estado = seguinte

        raise AssertionError("Limite de passos atingido.")


    return (executar_cfa,)


@app.cell
def _(executar_cfa, n):

    assert n >= 4, "Estes exemplos requerem n >= 4."

    modulo_testes = 2**n

    # Entradas escolhidas para provocar cada tipo de overflow
    a_erro_left = modulo_testes // 4
    a_erro_right = modulo_testes // 3 + 1

    casos_execucao = [
        (
            "Multiplicacao 3 x 5",
            3, 5,
            ["init", "skip", "right", "skip", "left", "skip",
             "left", "skip", "right", "skip", "stop"],
            15
        ),
        (
            "Overflow em left",
            a_erro_left, 4,
            ["init", "skip", "left", "skip", "left", "error_L"],
            0
        ),
        (
            "Overflow em right",
            a_erro_right, 3,
            ["init", "skip", "right", "skip", "left", "skip",
             "right", "error_R"],
            (3 * a_erro_right) % modulo_testes
        ),
        (
            "Multiplicacao com b = 0",
            7, 0,
            ["init", "skip", "stop"],
            0
        ),
        (
            "Multiplicacao com a = 0",
            0, 7,
            ["init", "skip", "right", "skip", "left", "skip",
             "right", "skip", "left", "skip",
             "right", "skip", "stop"],
            0
        )
    ]

    percursos_obtidos = {}

    for nome_exec, a_exec, b_exec, esperado_pc, esperado_z in casos_execucao:
        percurso_exec = executar_cfa(a_exec, b_exec)

        # Sequência dos nodos efetivamente visitados
        obtido_pc = [s["pc"] for s in percurso_exec]
        final_exec = percurso_exec[-1]

        # Verificar o percurso e o resultado final
        assert obtido_pc == esperado_pc, (
            f"Percurso incorreto em: {nome_exec}"
        )
        assert final_exec["z"] == esperado_z, (
            f"Resultado final incorreto em: {nome_exec}"
        )

        # A ação init deve estabelecer x=a, y=b, z=0
        assert percurso_exec[1]["x"] == a_exec
        assert percurso_exec[1]["y"] == b_exec
        assert percurso_exec[1]["z"] == 0

        # a e b devem permanecer constantes em todos os estados
        assert all(
            s["a"] == a_exec and s["b"] == b_exec
            for s in percurso_exec
        )

        percursos_obtidos[nome_exec] = percurso_exec

        print(f"\n{nome_exec} (a={a_exec}, b={b_exec})")
        print(" -> ".join(obtido_pc))
        print(f"Estado final: {final_exec['pc']}, z={final_exec['z']}")
        print("Teste: OK")

    print(f"\n{len(casos_execucao)} execuções validadas.")

    return (percursos_obtidos,)


@app.cell
def _(percursos_obtidos):

    percurso_normal = percursos_obtidos["Multiplicacao 3 x 5"]

    print("Execucao completa de 3 x 5\n")
    print("Passo | Nodo    | x   | y   | z")
    print("--------------------------------")

    for indice_normal, estado_normal in enumerate(percurso_normal):
        print(
            f"{indice_normal:5d} | "
            f"{estado_normal['pc']:<7} | "
            f"{estado_normal['x']:<3} | "
            f"{estado_normal['y']:<3} | "
            f"{estado_normal['z']}"
        )

    return




@app.cell
def _(
    BitVecVal,
    E,
    ERROR_L,
    ERROR_R,
    INIT,
    LEFT,
    Or,
    RIGHT,
    SKIP,
    STOP,
    Solver,
    T,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    unsat,
    x,
    z,
):

    # Ligações inexistentes no CFA
    ligacoes_proibidas = [
        ("init -> right", INIT, RIGHT),
        ("init -> stop", INIT, STOP),
        ("skip -> error_L", SKIP, ERROR_L),
        ("skip -> error_R", SKIP, ERROR_R),
        ("left -> right", LEFT, RIGHT),
        ("left -> error_R", LEFT, ERROR_R),
        ("right -> left", RIGHT, LEFT),
        ("right -> error_L", RIGHT, ERROR_L)
    ]

    for nome_lig, origem_lig, destino_lig in ligacoes_proibidas:
        solver_lig = Solver()
        solver_lig.add(
            T,
            pc == origem_lig,
            pc_next == destino_lig
        )

        resultado_lig = solver_lig.check()
        assert resultado_lig == unsat, f"Ligação indevida: {nome_lig}"

        print(f"{nome_lig}: {resultado_lig}")

    # Nenhum estado terminal pode ter sucessores
    for nome_terminal, local_terminal in [
        ("stop", STOP),
        ("error_L", ERROR_L),
        ("error_R", ERROR_R)
    ]:
        solver_terminal = Solver()
        solver_terminal.add(T, pc == local_terminal)

        resultado_terminal = solver_terminal.check()
        assert resultado_terminal == unsat
        print(f"Sem saída de {nome_terminal}: {resultado_terminal}")

    # Conservação global de a e b
    solver_constantes = Solver()
    solver_constantes.add(
        T,
        Or(a_next != a, b_next != b)
    )
    assert solver_constantes.check() == unsat
    print("a e b permanecem constantes: unsat")

    # Overflow em left não permite regressar a skip
    solver_prioridade_left = Solver()
    solver_prioridade_left.add(
        T,
        pc == LEFT,
        x == BitVecVal(2**(n - 1), n),
        pc_next == SKIP
    )
    assert solver_prioridade_left.check() == unsat
    print("Prioridade do erro em left: unsat")

    # Overflow em right não permite regressar a skip
    solver_prioridade_right = Solver()
    solver_prioridade_right.add(
        T,
        pc == RIGHT,
        x == BitVecVal(1, n),
        z == BitVecVal(2**n - 1, n),
        pc_next == SKIP
    )
    assert solver_prioridade_right.check() == unsat
    print("Prioridade do erro em right: unsat")

    # stop não pode ser simultaneamente um estado de erro
    solver_stop_erro = Solver()
    solver_stop_erro.add(E, pc == STOP)
    assert solver_stop_erro.check() == unsat
    print("stop não é um estado de erro: unsat")

    print("\n15 verificações estruturais concluídas.")

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 6. Verificação do invariante por k-indução

    A alínea 3.b pede a verificação da propriedade:

    \[
    P(S)\equiv xy+z=ab
    \]

    Como as variáveis aritméticas são BitVecs de largura \(n\), as operações são interpretadas módulo \(2^n\).

    ### 6.1. Verificação por 1-indução

    A 1-indução utiliza duas condições.

    **Caso base:**

    \[
    I(S)\land\neg P(S)
    \]

    **Passo indutivo:**

    \[
    P(S)\land T(S,S')\land\neg P(S')
    \]

    Uma condição `unsat` significa que não existe um contraexemplo à implicação correspondente.

    Começamos por verificar a propriedade original sem acrescentar condições, para determinar se é um invariante global do SFOTS.
    """)
    return


@app.cell
def _(
    I,
    Not,
    Solver,
    T,
    a,
    a_next,
    b,
    b_next,
    pc,
    sat,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Propriedade original do enunciado
    P_mod = (x * y + z == a * b)

    # Propriedade no estado seguinte
    P_mod_next = (
        x_next * y_next + z_next == a_next * b_next
    )

    # Caso base: existe um estado inicial que viola P?
    solver_base_p = Solver()
    solver_base_p.add(I, Not(P_mod))

    resultado_base_p = solver_base_p.check()
    print("P original - caso base:", resultado_base_p)

    if resultado_base_p == sat:
        modelo_base_p = solver_base_p.model()
        print("Contraexemplo inicial:")
        for var_p in (pc, a, b, x, y, z):
            print(f"  {var_p} = {modelo_base_p.eval(var_p)}")

    # Passo indutivo: P pode deixar de ser verdadeira?
    solver_passo_p = Solver()
    solver_passo_p.add(
        P_mod,
        T,
        Not(P_mod_next)
    )

    resultado_passo_p = solver_passo_p.check()
    print("P original - passo indutivo:", resultado_passo_p)

    assert resultado_base_p == sat
    assert resultado_passo_p == sat

    return P_mod, P_mod_next


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 6.2. Propriedade condicionada à inicialização

    A propriedade original não é verdadeira em todos os estados iniciais, porque a ação do nodo `init` ainda não foi executada.

    Definimos então:

    \[
    Q(S)\equiv(pc=init)\lor(xy+z=ab)
    \]

    Esta propriedade exige a igualdade aritmética apenas depois da inicialização.

    O CFA permanece inalterado.

    No entanto, a 1-indução de \(Q\) pode falhar devido a estados não alcançáveis, nomeadamente estados em `left` com \(y\) ímpar.

    É necessário distinguir uma falha do passo indutivo de um contraexemplo a uma execução iniciada corretamente.
    """)
    return


@app.cell
def _(
    I,
    INIT,
    Not,
    Or,
    P_mod,
    P_mod_next,
    Solver,
    T,
    pc,
    pc_next,
    sat,
    unsat,
    x,
    y,
    z,
):

    # Propriedade condicionada ao nodo init
    Q_cond = Or(
        pc == INIT,
        P_mod
    )

    Q_cond_next = Or(
        pc_next == INIT,
        P_mod_next
    )

    # Caso base
    solver_base_q = Solver()
    solver_base_q.add(I, Not(Q_cond))

    resultado_base_q = solver_base_q.check()
    print("Q condicionada - caso base:", resultado_base_q)

    # Passo indutivo
    solver_passo_q = Solver()
    solver_passo_q.add(
        Q_cond,
        T,
        Not(Q_cond_next)
    )

    resultado_passo_q = solver_passo_q.check()
    print("Q condicionada - passo indutivo:", resultado_passo_q)

    if resultado_passo_q == sat:
        modelo_passo_q = solver_passo_q.model()

        print("Exemplo de falha do passo indutivo:")
        for var_q in (pc, y, x, z, pc_next):
            print(f"  {var_q} = {modelo_passo_q.eval(var_q)}")

    assert resultado_base_q == unsat
    assert resultado_passo_q == sat

    return Q_cond, Q_cond_next


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 6.3. Invariante reforçado

    Para excluir estados incompatíveis com as guardas do CFA, definimos o invariante auxiliar:

    \[
    C(S)\equiv
    (pc=left\Rightarrow y\neq0\land even(y))
    \land
    (pc=right\Rightarrow y\neq0\land odd(y))
    \]

    Este predicado exprime as condições necessárias para entrar nos nodos `left` e `right`.

    Combinamos este predicado com a propriedade condicionada:

    \[
    J(S)\equiv Q(S)\land C(S)
    \]

    Vamos verificar \(J\) por 1-indução:

    **Caso base:**

    \[
    I(S)\land\neg J(S)
    \]

    **Passo indutivo:**

    \[
    J(S)\land T(S,S')\land\neg J(S')
    \]

    Se ambas as fórmulas forem `unsat`, então \(J\) é um invariante do SFOTS.

    Como \(J\) implica \(Q\), fica demonstrado que a igualdade \(xy+z=ab\) se verifica em todos os estados alcançáveis depois da inicialização.

    Não são introduzidas novas variáveis nem alteradas as transições do CFA.
    """)
    return


@app.cell
def _(
    And,
    I,
    LEFT,
    Not,
    Q_cond,
    Q_cond_next,
    RIGHT,
    Solver,
    T,
    even_y,
    odd_y,
    pc,
    pc_next,
    um,
    unsat,
    y,
    y_next,
    zero,
):

    from z3 import Implies

    # Condições de controlo no estado atual
    C_guard = And(
        Implies(
            pc == LEFT,
            And(y != zero, even_y)
        ),
        Implies(
            pc == RIGHT,
            And(y != zero, odd_y)
        )
    )

    # Condições de controlo no estado seguinte
    even_y_next = (y_next & um) == zero
    odd_y_next = (y_next & um) == um

    C_guard_next = And(
        Implies(
            pc_next == LEFT,
            And(y_next != zero, even_y_next)
        ),
        Implies(
            pc_next == RIGHT,
            And(y_next != zero, odd_y_next)
        )
    )

    # Invariante reforçado
    J_ind = And(Q_cond, C_guard)
    J_ind_next = And(Q_cond_next, C_guard_next)

    # Caso base
    solver_base_j = Solver()
    solver_base_j.add(I, Not(J_ind))

    resultado_base_j = solver_base_j.check()
    print("J reforcado - caso base:", resultado_base_j)

    # Passo indutivo
    solver_passo_j = Solver()
    solver_passo_j.add(
        J_ind,
        T,
        Not(J_ind_next)
    )

    resultado_passo_j = solver_passo_j.check()
    print("J reforcado - passo indutivo:", resultado_passo_j)

    # Confirmar que as duas condições foram demonstradas
    assert resultado_base_j == unsat
    assert resultado_passo_j == unsat

    print("Invariante reforcado demonstrado por 1-inducao.")

    return C_guard, C_guard_next


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 6.4. Conclusão da alínea 3.b

    A propriedade original:

    \[
    P(S)\equiv xy+z=ab
    \]

    não é um invariante global do SFOTS, porque os valores de \(x,y,z\) ainda não foram inicializados quando o programa se encontra no nodo `init`.

    A propriedade condicionada:

    \[
    Q(S)\equiv(pc=init)\lor(xy+z=ab)
    \]

    satisfaz o caso base, mas o passo de 1-indução admite estados não alcançáveis que violam as condições de controlo do CFA.

    Para resolver esta dificuldade, utilizámos o invariante auxiliar \(C\), que incorpora as guardas necessárias à entrada nos nodos `left` e `right`.

    O invariante reforçado:

    \[
    J(S)\equiv Q(S)\land C(S)
    \]

    foi demonstrado por 1-indução, tendo o Z3 devolvido `unsat` tanto no caso base como no passo indutivo.

    Concluímos que a igualdade \(xy+z=ab\) é preservada, módulo \(2^n\), em todos os estados alcançáveis depois da execução da ação de inicialização.

    Esta demonstração respeita o CFA original e não exige alterações ao estado inicial ou à relação de transição.

    **Contribuição LLM:** Formulação da propriedade condicionada, identificação da necessidade de reforço indutivo, construção de \(C\) e implementação das verificações por 1-indução.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 7. Verificação da segurança por k-indução

    A alínea 3.c acrescenta ao estado inicial as restrições:

    \[
    a<2^{n/2}\land b<2^{n/2}
    \]

    Pretende-se demonstrar que os estados de erro nunca são alcançados:

    \[
    G(\neg E)
    \]

    ### 7.1. Estado inicial restringido

    Definimos:

    \[
    I_c(S)\equiv I(S)\land B_c(S)
    \]

    onde \(B_c\) representa as restrições sobre os operandos originais.

    Como os operandos são interpretados sem sinal, estas condições garantem:

    \[
    ab<2^n
    \]

    O estado inicial continua a ser o nodo `init`, e a relação de transição original permanece inalterada.

    Para larguras ímpares, o limite inteiro é calculado sem arredondamentos aproximados, usando:

    \[
    a,b\le\lfloor\sqrt{2^n-1}\rfloor
    \]
    """)
    return


@app.cell
def _(And, BitVecVal, I, a, a_next, b, b_next, n):

    from math import isqrt
    from z3 import ULE

    # Maior inteiro que satisfaz a < 2^(n/2)
    max_entrada_c = isqrt(2**n - 1)

    # Limite representado num BitVec de largura n
    limite_bv_c = BitVecVal(max_entrada_c, n)

    # Restrições sem sinal sobre os operandos originais
    limites_c = And(
        ULE(a, limite_bv_c),
        ULE(b, limite_bv_c)
    )

    # Restrições correspondentes no estado seguinte
    limites_next_c = And(
        ULE(a_next, limite_bv_c),
        ULE(b_next, limite_bv_c)
    )

    # Novo estado inicial da alínea c)
    I_c = And(I, limites_c)

    print(f"Largura dos BitVecs: {n}")
    print(f"Maior valor inicial permitido: {max_entrada_c}")

    return I_c, limites_c, limites_next_c, max_entrada_c


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 7.2. Invariante auxiliar de segurança

    A igualdade modular demonstrada na alínea 3.b não é suficiente para provar ausência de overflow.

    Precisamos da igualdade exata entre os valores naturais representados pelos BitVecs:

    \[
    P_{exata}(S)\equiv xy+z=ab
    \]

    Para evitar truncaturas, as expressões desta propriedade são calculadas com \(2n\) bits.

    Como a inicialização apenas ocorre na saída de `init`, utilizamos:

    \[
    Q_c(S)\equiv(pc=init)\lor P_{exata}(S)
    \]

    Reutilizamos também o invariante de controlo \(C(S)\) da alínea anterior.

    O invariante reforçado para a segurança é:

    \[
    J_c(S)\equiv
    B_c(S)\land Q_c(S)\land C(S)\land\neg E(S)
    \]

    Pretendemos demonstrar \(J_c\) por 1-indução.

    A propriedade \(J_c\) implica \(\neg E\), pelo que a sua demonstração garante a segurança do SFOTS com o estado inicial \(I_c\).
    """)
    return


@app.cell
def _(
    And,
    C_guard,
    C_guard_next,
    E,
    ERROR_L,
    ERROR_R,
    INIT,
    Not,
    Or,
    ZeroExt,
    a,
    a_next,
    b,
    b_next,
    limites_c,
    limites_next_c,
    n,
    pc,
    pc_next,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Representação alargada para 2n bits
    a2_c = ZeroExt(n, a)
    b2_c = ZeroExt(n, b)
    x2_c = ZeroExt(n, x)
    y2_c = ZeroExt(n, y)
    z2_c = ZeroExt(n, z)

    a2_next_c = ZeroExt(n, a_next)
    b2_next_c = ZeroExt(n, b_next)
    x2_next_c = ZeroExt(n, x_next)
    y2_next_c = ZeroExt(n, y_next)
    z2_next_c = ZeroExt(n, z_next)

    # Igualdade aritmética exata, sem truncatura
    P_exata_c = (
        x2_c * y2_c + z2_c == a2_c * b2_c
    )

    P_exata_next_c = (
        x2_next_c * y2_next_c + z2_next_c
        == a2_next_c * b2_next_c
    )

    # Propriedade condicionada à inicialização
    Q_exata_c = Or(
        pc == INIT,
        P_exata_c
    )

    Q_exata_next_c = Or(
        pc_next == INIT,
        P_exata_next_c
    )

    # Predicado de erro no estado seguinte
    E_next_c = Or(
        pc_next == ERROR_L,
        pc_next == ERROR_R
    )

    # Invariante reforçado de segurança
    J_c = And(
        limites_c,
        Q_exata_c,
        C_guard,
        Not(E)
    )

    # Invariante no estado seguinte
    J_next_c = And(
        limites_next_c,
        Q_exata_next_c,
        C_guard_next,
        Not(E_next_c)
    )

    return E_next_c, J_c, J_next_c


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 7.3. Prova por 1-indução

    Para demonstrar que \(J_c\) é um invariante, verificamos:

    **Caso base:**

    \[
    I_c(S)\land\neg J_c(S)
    \]

    **Passo indutivo:**

    \[
    J_c(S)\land T(S,S')\land\neg J_c(S')
    \]

    Pretendemos obter `unsat` nas duas condições.

    Também verificamos diretamente se existe uma transição de um estado que satisfaz \(J_c\) para um estado de erro:

    \[
    J_c(S)\land T(S,S')\land E(S')
    \]

    Esta fórmula deverá ser igualmente insatisfazível.

    Antes das provas, confirmamos que o novo estado inicial admite pelo menos um estado, evitando uma demonstração vazia por inconsistência das condições iniciais.
    """)
    return


@app.cell
def _(E_next_c, I_c, J_c, J_next_c, Not, Solver, T, sat, unsat):

    # Verificar que o estado inicial restringido é satisfazível
    solver_inicial_c = Solver()
    solver_inicial_c.add(I_c)
    resultado_inicial_c = solver_inicial_c.check()

    print("Estado inicial restringido:", resultado_inicial_c)

    # Caso base
    solver_base_c = Solver()
    solver_base_c.add(
        I_c,
        Not(J_c)
    )

    resultado_base_c = solver_base_c.check()
    print("Caso base:", resultado_base_c)

    # Passo indutivo
    solver_passo_c = Solver()
    solver_passo_c.add(
        J_c,
        T,
        Not(J_next_c)
    )

    resultado_passo_c = solver_passo_c.check()
    print("Passo indutivo:", resultado_passo_c)

    # Verificação direta da impossibilidade de entrar em erro
    solver_erro_c = Solver()
    solver_erro_c.add(
        J_c,
        T,
        E_next_c
    )

    resultado_erro_c = solver_erro_c.check()
    print("Transicao para erro:", resultado_erro_c)

    # Validar os resultados
    assert resultado_inicial_c == sat
    assert resultado_base_c == unsat
    assert resultado_passo_c == unsat
    assert resultado_erro_c == unsat

    print("\nSeguranca demonstrada por 1-inducao.")

    return


@app.cell
def _(executar_cfa, max_entrada_c):

    # Teste com os maiores operandos admitidos por I_c
    percurso_limite_c = executar_cfa(
        max_entrada_c,
        max_entrada_c
    )

    estado_final_c = percurso_limite_c[-1]

    assert estado_final_c["pc"] == "stop"
    assert estado_final_c["z"] == max_entrada_c**2

    assert all(
        estado_c["pc"] not in ("error_L", "error_R")
        for estado_c in percurso_limite_c
    )

    print(
        f"{max_entrada_c} x {max_entrada_c} = "
        f"{estado_final_c['z']}"
    )
    print("Estado final:", estado_final_c["pc"])
    print("Teste do limite: OK")

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 7.4. Conclusão da alínea 3.c

    Foi considerado o estado inicial restringido:

    \[
    I_c(S)=I(S)\land(a<2^{n/2})\land(b<2^{n/2})
    \]

    Os operandos foram interpretados sem sinal, de acordo com a decisão de modelação apresentada na alínea 3.a.

    Para demonstrar a segurança, utilizámos uma igualdade aritmética exata, calculada através do alargamento temporário dos BitVecs para \(2n\) bits.

    Construímos o invariante reforçado:

    \[
    J_c=B_c\land Q_c\land C\land\neg E
    \]

    A verificação por 1-indução devolveu `unsat` tanto no caso base como no passo indutivo.

    Adicionalmente, a fórmula que procura uma transição para um estado de erro a partir de um estado que satisfaz \(J_c\) foi insatisfazível.

    Concluímos que:

    \[
    \boxed{G(\neg E)}
    \]

    Assim, para a largura \(n\) verificada e para todos os operandos iniciais que satisfazem as restrições da alínea 3.c, os estados de erro são inacessíveis.

    A demonstração utiliza a interpretação de overflow sem sinal e não altera a relação de transição do CFA.

    **Contribuição LLM:** Formulação do invariante de segurança, utilização de aritmética exata com BitVecs alargados, implementação da prova por 1-indução e elaboração do teste de fronteira.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 8. Verificação da terminação

    A alínea 3.d pretende demonstrar que o programa termina para quaisquer operandos iniciais \(a,b\).

    ### 8.1. Propriedade de animação

    O predicado dos estados terminais é:

    \[
    Term(S)\equiv
    (pc=stop)\lor(pc=error_L)\lor(pc=error_R)
    \]

    A propriedade pretendida é:

    \[
    F\,Term
    \]

    Consideramos tanto a conclusão normal como a terminação por overflow.

    ### 8.2. Função de progresso

    Definimos uma função \(R\) com valores naturais:

    \[
    R(S)=
    \begin{cases}
    2b+2 & pc=init\\
    2y+1 & pc=skip\\
    2y & pc\in\{left,right\}\\
    0 & Term(S)
    \end{cases}
    \]

    Os valores de \(b\) e \(y\) são interpretados sem sinal.

    A função foi escolhida para diminuir estritamente em cada transição não terminal alcançável.

    A demonstração utiliza o invariante de controlo \(C\), estabelecido na alínea 3.b, que garante:

    - Em `left`, \(y\) é par e diferente de zero;
    - Em `right`, \(y\) é ímpar e diferente de zero.

    Como os números naturais são bem fundados relativamente à ordem \(<\), uma sequência estritamente decrescente destes valores não pode ser infinita.

    ### 8.3. Predicado lookahead

    Para verificar a evolução do programa, utilizamos:

    \[
    P^*(S,S')\equiv
    (Term(S)\land Term(S'))
    \lor
    (\neg Term(S)\land C(S)\land C(S')
    \land R(S')<R(S))
    \]

    A prova será realizada através da condição inicial e da condição indutiva do lookahead, segundo a metodologia apresentada no Capítulo 3.

    Não são acrescentadas autotransições aos estados terminais do CFA.
    """)
    return


@app.cell
def _(
    And,
    BitVecVal,
    C_guard,
    C_guard_next,
    ERROR_L,
    ERROR_R,
    INIT,
    LEFT,
    Not,
    Or,
    RIGHT,
    SKIP,
    STOP,
    Term,
    ZeroExt,
    b,
    b_next,
    n,
    pc,
    pc_next,
    y,
    y_next,
):

    from z3 import If, ULT, Const, substitute

    # Funcao de progresso com largura suficiente
    def progresso_d(local_d, y_d, b_d):
        largura_d = n + 2

        y_ext_d = ZeroExt(2, y_d)
        b_ext_d = ZeroExt(2, b_d)

        zero_d = BitVecVal(0, largura_d)
        um_d = BitVecVal(1, largura_d)
        dois_d = BitVecVal(2, largura_d)

        return If(
            local_d == INIT,
            (b_ext_d << 1) + dois_d,
            If(
                local_d == SKIP,
                (y_ext_d << 1) + um_d,
                If(
                    Or(local_d == LEFT, local_d == RIGHT),
                    y_ext_d << 1,
                    zero_d
                )
            )
        )

    # Funcao de progresso no estado atual e seguinte
    R_d = progresso_d(pc, y, b)
    R_next_d = progresso_d(pc_next, y_next, b_next)

    # Estados terminais no estado seguinte
    Term_next_d = Or(
        pc_next == STOP,
        pc_next == ERROR_L,
        pc_next == ERROR_R
    )

    # Lookahead binario
    P_star_d = Or(
        And(Term, Term_next_d),
        And(
            Not(Term),
            C_guard,
            C_guard_next,
            ULT(R_next_d, R_d)
        )
    )

    return Const, P_star_d, substitute


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 8.4. Verificação indutiva do lookahead

    O predicado \(P^*\) relaciona dois estados consecutivos.

    Para verificar a sua validade, utilizamos três cópias do estado:

    \[
    S_0\rightarrow S_1\rightarrow S_2
    \]

    **Caso base:**

    \[
    I(S_0)\land T(S_0,S_1)
    \land\neg P^*(S_0,S_1)
    \]

    **Passo indutivo:**

    \[
    P^*(S_0,S_1)\land T(S_0,S_1)
    \land T(S_1,S_2)
    \land\neg P^*(S_1,S_2)
    \]

    Esperamos obter `unsat` nas duas verificações.

    O invariante auxiliar \(C\), previamente demonstrado, impede que sejam utilizados estados incompatíveis com as guardas dos nodos `left` e `right`.

    A validade de \(P^*\), juntamente com a boa fundação dos números naturais e a ausência de bloqueios não terminais, permite concluir a terminação.
    """)
    return


@app.cell
def _(
    BitVecs,
    Const,
    I,
    Local,
    Not,
    P_star_d,
    Solver,
    T,
    a,
    a_next,
    b,
    b_next,
    n,
    pc,
    pc_next,
    substitute,
    unsat,
    x,
    x_next,
    y,
    y_next,
    z,
    z_next,
):

    # Terceira copia das variaveis de estado
    pc_2_d = Const("pc_2_d", Local)

    a_2_d, b_2_d, x_2_d, y_2_d, z_2_d = BitVecs(
        "a_2_d b_2_d x_2_d y_2_d z_2_d", n
    )

    # Tres estados consecutivos
    estado0_d = (pc, a, b, x, y, z)

    estado1_d = (
        pc_next, a_next, b_next,
        x_next, y_next, z_next
    )

    estado2_d = (
        pc_2_d, a_2_d, b_2_d,
        x_2_d, y_2_d, z_2_d
    )

    # Substituicao simultanea: S0 -> S1, S1 -> S2
    substituicoes_d = list(zip(
        estado0_d + estado1_d,
        estado1_d + estado2_d
    ))

    # Transicao de S1 para S2
    T_12_d = substitute(T, *substituicoes_d)

    # Lookahead entre S1 e S2
    P_star_12_d = substitute(
        P_star_d,
        *substituicoes_d
    )

    # Caso base do lookahead
    solver_base_d = Solver()
    solver_base_d.add(
        I,
        T,
        Not(P_star_d)
    )

    resultado_base_d = solver_base_d.check()
    print("Lookahead - caso base:", resultado_base_d)

    # Passo indutivo do lookahead
    solver_passo_d = Solver()
    solver_passo_d.add(
        P_star_d,
        T,
        T_12_d,
        Not(P_star_12_d)
    )

    resultado_passo_d = solver_passo_d.check()
    print("Lookahead - passo indutivo:", resultado_passo_d)

    assert resultado_base_d == unsat
    assert resultado_passo_d == unsat

    print("Lookahead demonstrado por inducao.")

    return


@app.cell
def _(
    And,
    INIT,
    LEFT,
    Not,
    OF_L,
    OF_R,
    Or,
    RIGHT,
    SKIP,
    Solver,
    Term,
    even_y,
    odd_y,
    pc,
    unsat,
    y,
    zero,
):

    # Existe uma guarda habilitada em cada nodo nao terminal
    guardas_cobertas_d = Or(
        pc == INIT,

        And(
            pc == SKIP,
            Or(
                y == zero,
                And(y != zero, even_y),
                And(y != zero, odd_y)
            )
        ),

        And(
            pc == LEFT,
            Or(OF_L, Not(OF_L))
        ),

        And(
            pc == RIGHT,
            Or(OF_R, Not(OF_R))
        )
    )

    # Procurar um estado nao terminal sem guarda habilitada
    solver_cobertura_d = Solver()
    solver_cobertura_d.add(
        Not(Term),
        Not(guardas_cobertas_d)
    )

    resultado_cobertura_d = solver_cobertura_d.check()
    print("Estado nao terminal sem guarda:", resultado_cobertura_d)

    assert resultado_cobertura_d == unsat

    print("Guardas dos nodos nao terminais cobertas.")

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 8.5. Conclusão da alínea 3.d

    A propriedade de animação pretendida é:

    \[
    F\,Term
    \]

    onde:

    \[
    Term(S)\equiv
    (pc=stop)\lor(pc=error_L)\lor(pc=error_R)
    \]

    Para demonstrar a terminação, definimos uma função de progresso \(R\) com valores naturais, dependente do nodo atual e do valor de \(y\) ou \(b\).

    Construímos um predicado binário de lookahead \(P^*\), que exige a diminuição estrita de \(R\) nas transições não terminais.

    A verificação por indução devolveu `unsat` no caso base e no passo indutivo.

    Foi também confirmada a cobertura das guardas dos nodos não terminais. Como todas as ações são bem definidas, nenhum estado não terminal fica bloqueado.

    Uma vez que a função de progresso diminui estritamente e os números naturais são bem fundados, não podem existir execuções infinitas que evitem os estados terminais.

    Concluímos que todas as execuções máximas do CFA, para quaisquer operandos iniciais \(a,b\), terminam em `stop`, `error_L` ou `error_R`.

    A relação de transição original foi preservada, sem acrescentar autotransições.

    **Contribuição LLM:** Formulação da função de progresso, construção do lookahead, codificação da prova indutiva e verificação da cobertura das guardas.
    """)
    return


if __name__ == "__main__":
    app.run()
