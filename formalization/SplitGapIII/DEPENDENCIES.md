# Procedencia

PROVENANCE.json conserva la procedencia de la base Lean de la Parte II. El manifiesto Lake fija todas las dependencias externas.

- Base Lean de Split Gap II en https://github.com/jtraverso/split-clique-partition-gap-ii/tree/3e009f6f9a0103363b1714e1583f12a0a731441b/lean
- Galvin, módulos GalvinLib, GalvinMultigraph, Konig y LeanPool en https://github.com/jtraverso/galvin-dinitz/tree/84dcda4c2a760f2b52b7e813affe7e6968f8bfce
- Split Gap I, módulos R417, R434 y complementos de GapExtremal en https://github.com/jtraverso/split-clique-partition-gap/tree/ab463d8f4841101ba5c28047def8553b0c23249f . Freeze fuente split-gap-lean-v1.0.zip, SHA-256 99b817230be0cfad9147a6e47cd232080aa96ce7b18076d1454ce1dbee6bf811.

MODULES.txt lista los módulos locales. Mathlib y sus dependencias se obtienen a través de Lake.
