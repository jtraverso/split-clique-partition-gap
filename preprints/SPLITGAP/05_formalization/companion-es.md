# Guía de la formalización de *Gaps aditivos casi cuadráticos para particiones de aristas en cliques de grafos split*

*Preprint 1.0 · 21 de noviembre de 2026*

## Alcance del enunciado formal

Para cada real $\eta>0$, el teorema del corolario 1.2 proporciona un umbral $N$. Para cada entero $n\ge N$ da un tipo finito de cardinalidad $n$ y un grafo split conexo sobre ese tipo. La cota inferior compara el mínimo número de piezas de una partición exacta de aristas y el mínimo coste de una partición fraccional exacta. Ambos óptimos admiten cliques de todo orden a partir de dos. El teorema no presupone la existencia de un grafo auxiliar, de un empaquetamiento ni de un conjunto de densidad grande. [Corolario 1.2 en Lean](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/UniversalR434.lean) · [Gap](https://github.com/jtraverso/split-clique-partition-gap/blob/main/GapExtremal/Defs.lean) · [Números de partición](https://github.com/jtraverso/split-clique-partition-gap/blob/main/GraphBase/Clique/Partition.lean)

## Cotas cuantitativas y estructurales

El teorema 1.1 da una constante absoluta $k>0$ y un umbral $N$. Para todo $n\ge N$, Lean construye un grafo split conexo de orden exactamente $n$ cuyo gap es al menos $k n^2(\log n)^{-5/2}\exp[-2\sqrt{\log(24/7)\log n}]$. Se toma $\epsilon=7/(1080j)$. El recuento formal de la grilla da densidad al menos $7/24-30\epsilon$ cuando $\epsilon m\ge43$ y $3\epsilon\le1/12$. Esta cota unilateral basta para el teorema 1.1. El lema 6.1 da la estimación geométrica bilateral del manuscrito. [Teorema final](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogGap.lean) · [Estimación del orden](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogOrder.lean) · [Recuento en la grilla](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/DensityThreshold.lean)

En el lema 4.1 se verifican tanto la cota superior de 16 triángulos locales como el ejemplo que la alcanza. El manuscrito usa paridad. Lean proyecta el empaquetamiento sobre las tres capas de pares de colores. Con 17 triángulos faltaría una arista en cada capa. Una suma con signo de índices de roles muestra que los extremos de esas aristas son compatibles y que completan la descomposición prohibida. El recuento en todos los bloques da $6\tau\le |X|+3z$. La estimación de energía tiene numerador $6\tau$ y denominador $27(1+2R/\delta)$, como en el lema 4.1. El factor seis también aparece en la cota finita que utiliza el teorema final. [Empaquetamiento local](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/LocalPacking.lean) · [Bloques y defecto](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/CoreDefect.lean) · [Cota finita](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/FiniteR434.lean)

El enunciado formal de los teoremas 1.1 y 1.4 es `universal_R434_linear`. Proporciona un grafo split de orden exactamente $n$ con la cota del gap y `SurvivesCuts G ((n+4)/5)` en el mismo grafo. Este predicado exige que el grafo siga conexo tras eliminar cualquier conjunto de menos de $\lceil n/5\rceil$ vértices. Los nuevos vértices se añaden como aislados al residual ya construido y pertenecen a todas las vecindades de hosts en el grafo split. Por proyección se conserva la cota superior sobre el puntaje entero. Por extensión se conserva el testigo fraccional. Estos dos certificados bastan para la cota inferior del gap. [Aislados del residual](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/ResidualIsolates.lean) · [Hosts universales](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/UniversalHosts.lean) · [Teorema conjunto](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogGap.lean)

El teorema `universal_R434_compact` utiliza el mismo coloreo con 24 clases y amplía las vecindades mediante roles completos. Da una cota para los cortes de orden $n/\sqrt{\log n}$. Para el gap solo, `universal_R434_grouped` asigna cada arista de roles a uno de cuatro matchings de su capa y usa un host de punto medio común para todos los pares de una clase del matching. Lean comprueba que las vecindades ampliadas son independientes en el residual y que las asignaciones siguen siendo matchings. Hay 66 pares de roles siempre ausentes y $12\cdot24j$ etiquetas geométricas por posición. Con los 15 roles del núcleo, el grafo de base utiliza $(81+288j)m^{2j}$ vértices. [Coloreo exterior](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/EHPSCompactExterior.lean) · [Matchings de roles](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/RoleMatchings.lean) · [Agrupación de hosts](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/GroupedHosts.lean) · [Orden del grafo](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/GroupedGap.lean)

El corolario 1.3 se deduce en el manuscrito de la inclusión de los grafos split entre los cordales y del teorema uniforme de redondeo [2, teorema 1.10]. El módulo raíz comprueba las cotas inferiores constructivas en grafos split. Los dos límites para el máximo cordal utilizan además la cota superior publicada.

## El corolario de empaquetamiento mixto

El teorema `universal_R434_linear_mixed` da la misma cota asintótica y la garantía de conectividad con `gapWithFracFour`. Esta cantidad es el coste entero mínimo sin restricción de tamaño menos el coste fraccional mínimo con piezas de orden a lo sumo cuatro. La prueba conserva la cota de tres vértices en el soporte del testigo fraccional afín al añadir aislados al residual y al completar la solución con hosts. Restringir también las piezas enteras a orden cuatro solo puede aumentar el gap. Mediante la identidad entre particiones exactas de orden a lo sumo cuatro y ganancias de empaquetamiento mixto, el corolario 7.2 expresa la cota en la notación del artículo IV. [Teorema principal](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogGap.lean) · [Coste fraccional restringido](https://github.com/jtraverso/split-clique-partition-gap/blob/main/GapExtremal/Completion.lean) · [Completación con hosts](https://github.com/jtraverso/split-clique-partition-gap/blob/main/GapExtremal/Bridge.lean)

## Dos cálculos de la demostración

**Vértices compartidos entre bloques.** Cada bloque afín tiene 54 aristas. Los 36 triángulos de la tabla local tienen peso $1/2$ cada uno y saturan todas las aristas. Como cada triángulo ahorra dos piezas, contribuyen 36 al puntaje residual del bloque. Cada arista pertenece a un único bloque, por lo que el cálculo se multiplica por el número de bloques. La obstrucción entera de un bloque requiere otro argumento. Fijemos una ordenada en el origen $x$ y direcciones distintas $a,b$ tales que $(a+b)/2$ esté disponible. Las posiciones $x,x+a,x+a+b$ realizan las tres direcciones permitidas. Para una terna de roles que sobrevive forman un triángulo con aristas de tres bloques distintos. La sección 4 trata precisamente este caso. [Certificado local](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/LocalH54.lean) · [Cálculo de direcciones](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/CoreDirections.lean)

**Origen del coeficiente.** Sean $\rho$ la densidad de un factor plano y $c=-\log\rho$. Al tomar $j$ factores se pierde $\rho^j$. El potencial reescalado cuesta otro factor de orden $jm^2$, donde $m$ es el módulo de la grilla y $2j\log m$ es aproximadamente $\log n$. En el orden principal, el logaritmo negativo del gap relativo queda acotado por $cj+(\log n)/j$. Los dos términos coinciden para $j=\sqrt{(\log n)/c}$. La densidad plana puede aproximarse a $7/24$ por debajo, lo que da $2\sqrt{\log(24/7)}$. Para el corolario 1.2 se fija el soporte plano antes de hacer crecer $n$. En el teorema 1.1 el soporte varía con $j$ y se conserva el coeficiente límite. La optimalidad de este coeficiente para grafos split sigue abierta. [Umbral de densidad](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/DensityThreshold.lean) · [Elección de parámetros](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/UniformOrder.lean)

**Multiplicadores explícitos.** Sean $c=\log(24/7)$ y $K=200(1080/7)^2$. El prefactor del gap en cada teorema es
$$
 k(A)=\frac{2c^{5/2}e^{-2-2c}}{27A^2(1+K)}.
$$
El teorema 1.4 utiliza $A=78375$ y $k(A)\approx4.9144\cdot10^{-20}$. La construcción compacta utiliza $A=3135$ y $k(A)\approx3.0715\cdot10^{-17}$, con cota de conectividad al menos $\sqrt c\,n/(Ae\sqrt{\log n})$. La agrupada utiliza $A=369$ y $k(A)\approx2.2170\cdot10^{-15}$ para grafos split conexos. Las tres estimaciones toman $\epsilon=7/(1080j)$. Para $\epsilon=y/j$, el multiplicador dominante de las estimaciones del potencial y de la densidad es proporcional a $y^2(1-30y/(7/24))$ y alcanza su máximo en $y=7/1080$. [Cálculo de parámetros](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogOrder.lean)

El desplazamiento en la estimación con signo admite un programa lineal con dos restricciones. Normalizamos $0\le f\le R$ y escribimos $g=f-u$. Una cota superior $M$ para el valor absoluto de un precio negativo debe satisfacer $M\ge u$ y $M\ge 2R-2u$ si solo se utiliza este rango. Ponderar estas desigualdades por $2/3$ y $1/3$ da $M\ge2R/3$. La elección $u=2R/3$ alcanza la igualdad. Mejorar la cota requiere información adicional al desplazamiento uniforme y a la oscilación de $f$.

## Correspondencia entre la demostración y Lean

| Manuscrito | Resultado formal | Comprobación |
|---|---|---|
| §2, transferencia a un grafo split | [Transferencia de orden exacto](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/ExactGraphTransfer.lean) | La diferencia entre un puntaje fraccional factible y una cota superior de los puntajes enteros acota el gap del grafo por debajo. El manuscrito deduce además una identidad entre ahorros óptimos. |
| §3 y apéndice A, obstrucción local | [Grafo local y precios](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/LocalH54.lean) | Hay 45 triángulos y 36 pertenecen al soporte fraccional. El orden de los tipos de aristas determina la correspondencia con los precios del apéndice. |
| §4, piezas casi óptimas | [Holgura tripartita](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/TripartiteSlack.lean) · [Triángulos de holgura nula](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/TightTriangles.lean) | Una pieza de holgura nula se parte en triángulos. La holgura positiva acota el número de aristas apartadas. |
| §4, bloques afines y energía | [Defecto del núcleo](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/CoreDefect.lean) · [Puntaje fraccional](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/CoreFractional.lean) | La estimación entera admite triángulos mixtos. El testigo fraccional solo utiliza triángulos internos a los bloques. |
| §5, hosts y relleno | [Hosts de punto medio](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/MidpointHosts.lean) · [Cota del producto](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/EHPSHostTransfer.lean) | El presupuesto compacto es $255+2880j$ por posición. El teorema 1.4 utiliza $25(255+2880j)$ para dar cabida a los vértices universales y sus hosts. |
| §6, construcción plana | [Región](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/EHPSRegion.lean) · [Potencial](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/EHPSPotential.lean) · [Densidad en la grilla](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/EHPSDensity.lean) | Lean demuestra las desigualdades de densidad y punto medio utilizadas en el artículo. |
| §6, cota final | [Grafo finito](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/FiniteR434.lean) · [Corolario 1.2](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/UniversalR434.lean) · [Teorema 1.1](https://github.com/jtraverso/split-clique-partition-gap/blob/main/R434/PolylogGap.lean) | Se elige un módulo impar y se añaden hosts hasta alcanzar el orden prescrito. |
| §§1 y 7, consecuencias | [Manuscrito](../01_manuscript/split-gap-es.md) | La cota superior cordal utiliza el teorema de redondeo citado. Los resultados sobre triángulos y empaquetamientos mixtos se deducen por completación. Para el segundo se utiliza el testigo fraccional de tamaño restringido. |

El ejemplo del apéndice A también se puede verificar con la biblioteca estándar de Python. El verificador lee las siete ternas suprimidas y el empaquetamiento del manuscrito, y agota las asignaciones que podrían cubrir 17 aristas distintas del primer par de colores.

```sh
python audit/check_local_packing.py
```

## Generación de un grafo

Desde la raíz del repositorio, el primer comando escribe la lista completa de aristas, numerando los vértices desde cero. El segundo reconstruye el ejemplo, comprueba cada par asignado, cada matching y cada vecindad independiente, y calcula el hash de la lista de aristas.

~~~sh
python witness.py --dimension 1 --modulus 3 --order 4620 --edges example.edges
python audit/check_robust_witness.py
~~~

El generador y el ejemplo finito usan vecindades ampliadas con roles completos. El ejemplo tiene 135 vértices en el núcleo, tres hosts de relleno y 64 962 aristas. Cada host tiene al menos nueve vecinos en el núcleo. Eliminar los nueve vecinos de un host de relleno lo aísla. Hay una dirección y, por tanto, nueve bloques. Al tomar un potencial constante de oscilación cero en el lema 4.1 se obtiene $\Delta(G)\ge2$ para este ejemplo. El teorema asintótico requiere orden suficientemente grande. Para seleccionar parámetros automáticamente se usa `python witness.py --order N --edges graph.edges` con un entero suficientemente grande en lugar de `N`. Al omitir `--edges` se imprimen los parámetros y los recuentos. [Generador](https://github.com/jtraverso/split-clique-partition-gap/blob/main/witness.py) · [Certificado del ejemplo](https://github.com/jtraverso/split-clique-partition-gap/blob/main/audit/robust-example.json)

## Reproducción de la comprobación formal

El [archivo de fuentes](split-gap-lean-v1.0.zip) contiene un proyecto Lean portable. Desde su directorio `lean` se ejecuta

```sh
lake exe cache get
lake build SplitGap
lake build +R434.CheckStrengthenings
```

El paquete fija la versión de Lean y las revisiones de sus dependencias. El registro de compilación identifica las fuentes, su revisión, los módulos compilados y los axiomas. La consulta cubre el gap original, la conectividad, las cotas compacta y agrupada y la cota mixta. [Registro de compilación](../02_validation/v1.0/lean/status.json) · [Consulta de axiomas](../02_validation/v1.0/lean/checking-axioms.log) · [Instrucciones de reproducción](../03_reproducibility/README.md)


## Procedencia y atribución

El cálculo de perfiles fraccionales del artículo I y el extremo cordal del artículo II motivaron la comparación de los óptimos entero y fraccional en un mismo grafo. El artículo III establece la cota superior entera en grafos split y plantea el problema 12.1. La transferencia exacta de la sección 2 se apoya en las asignaciones a hosts del artículo V. Entre los antecedentes citados, las cotas inferiores para coberturas y empaquetamientos de la §5 de Balogh et al. amplifican obstrucciones finitas. La densidad aritmética, el potencial y el coeficiente correspondiente en el problema sin progresiones son de Elsholtz, Hunter, Proske y Sauermann. Aquí el conjunto de direcciones conserva sus progresiones y estimamos su coste en un empaquetamiento entero. [Artículo III](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/3cbd90eed41af7e86ac6f1f4b8c796e20a5e661f/preprints/PAPER_III) · [Artículo V](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/3cbd90eed41af7e86ac6f1f4b8c796e20a5e661f/preprints/PAPER_V) · [Balogh et al.](https://arxiv.org/html/2412.05522v3) · [Elsholtz et al.](https://arxiv.org/html/2406.12290v1)


Los archivos importados de la formalización anterior conservan sus avisos de derechos de autor. Para los archivos bajo Apache 2.0 se incluye el [texto de la licencia](https://github.com/jtraverso/split-clique-partition-gap/blob/main/audit/LICENSE-Apache-2.0.txt).



El certificado local de quince vértices se comprobó con Certo-Math v0.40.0. [Certificado R419](https://github.com/jtraverso/certo-math/blob/0590da36a2af900b9f23d9d292aac62eb6b06ca9/research/R419/NOTE.md).
