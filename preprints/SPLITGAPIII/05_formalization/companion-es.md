# Guía de la formalización de Recuperación de descomposiciones en triángulos con anfitrión tras borrados aleatorios en grafos split

## Lectura de los enunciados formales

El preprint usa el archivo de fuentes del 24 de noviembre de 2026. La sección 7 indica su SHA-256 y los nombres de las declaraciones principales. Los PDF de ambos manuscritos incluyen el ZIP como adjunto. El archivo de auditoría imprime los axiomas de los que dependen 77 declaraciones del espacio de nombres `SplitGapIII`.

El resultado sobre el soporte seleccionado es el Teorema 1 del preprint (Teorema 5 en la numeración original del suplemento). El lema `hosted_clique_deficit_mem` traduce las correcciones enteras de margen nulo a una afirmación sobre el retículo físico de triángulos, bajo las hipótesis de disponibilidad de los intercambios. El lema `selected_hinge_condition` deduce H4 a partir de un conteo de completaciones ordenadas. Las estimaciones de concentración y el argumento de cortes que producen un mismo soporte aleatorio adecuado están en la sección 5 y el apéndice B.

El Teorema 2 (antes Teorema 6) compara estadísticas a dos escalas. El lema `hosted_pasch_one_block` identifica un bloque mediante los cuatro triángulos con anfitrión y las condiciones que asignan cada base a un bloque. Dadas la semilla seleccionada, las hipótesis físicas y las cotas que comparan los objetivos de la semilla con los de referencia, `selected_decomposition_with_reference_targets` proporciona una descomposición común. La sección 6 compara los objetivos en la construcción aleatoria y deduce ambos coeficientes asintóticos. El Teorema 3 (antes Teorema 1) aplica la construcción a la brecha. El resultado en Lean para todos los órdenes usa copias adicionales de anfitriones. La sección 2 demuestra analíticamente el umbral óptimo para una sola reserva.

## Reproducción de la auditoría de declaraciones

Extraiga el ZIP en un directorio vacío. El archivo de la cadena de herramientas especifica Lean 4.35.0-rc3. El manifiesto de Lake fija Mathlib y la biblioteca de absorción física. Desde el directorio extraído, ejecute

```sh
lake exe cache get
lake build SplitGapIII
lake env lean SplitGapIIIAudit.lean
```

Compare los nombres de las declaraciones y sus listas de axiomas con `AUDIT.txt` en el ZIP. Los finales de línea pueden diferir. El directorio de validación incluye una ejecución con dependencias compiladas. La suma de verificación identifica las fuentes exactas y el informe histórico.

## Correspondencia de numeración

| Borrador de revisión 0.5 | Preprint 1.0 |
|---|---|
| Teorema 5, soporte equilibrado | Teorema 1 |
| Teorema 6, recuperación estadística | Teorema 2 |
| Teorema 1, brecha y conectividad | Teorema 3 |
| Teorema 2, listas aleatorias de anfitriones | Teorema 4 |
| Lema 3, dos órdenes de las coordenadas | Lema 5 |
| Proposición 4, cupos deterministas | Proposición 6 |
| Lema 6.1, localización de Pasch | Lema 7 |

Las trece ecuaciones numeradas conservan la numeración del borrador. El manuscrito y el archivo de fuentes están disponibles en el repositorio de la serie. <https://github.com/jtraverso/split-clique-partition-gap/tree/main/preprints/SPLITGAPIII>
