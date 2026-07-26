# 如何使用这份 Lean 4 + mathlib 形式化证明

## 1. 这份形式化做了什么

Lean 不是把论文的 TeX 公式重新排版一遍，而是把论证拆成：

1. **对象的精确定义**：有限税元集、树、split、ordered adjacent
   correction、principal chart、bridge reversal、四类平方、quartet
   kernel 等；
2. **每个中间恒等式**：有限和换序、指标集合分拆、系数提取、平方
   配方、反向 chart 的系数运输、边界项抵消；
3. **最终定理链**：A.30、`f₁ ≥ 0`、有限计数不等式、归一化上界以及
   极值比例趋于 `2/3`。

Lean 的 kernel 会逐条检查这些定义和证明项是否满足类型和逻辑规则。
如果某个指标集合写错、某个系数少了 `1/2`、某次换序不合法，通常就
无法通过编译。

## 2. 项目位置

```text
bandelt-dress-quartet-lean/formalization
```

有限树、quartet split、图论、随机重标号和最大值基础设施已经以
最小传递依赖集的形式内置在：

```text
formalization/QuartetDistance
```

因此现在只需保留仓库中的 `formalization` 文件夹，不再要求
同级目录存在 `quartet_lean_reference`。所内置的 10 个模块、来源
commit 和 MIT 许可证见：

```text
VENDORED_MODULES.md
THIRD_PARTY_NOTICES.md
third_party/quartet_distance_bandelt_dress/LICENSE
```

所用版本已经固定：

```text
Lean 4.32.0
mathlib v4.32.0
```

## 3. 最简单的完整检查

在终端进入项目目录：

```bash
cd bandelt-dress-quartet-lean/formalization
lake build
```

只有出现

```text
Build completed successfully
```

才表示当前全部 Lean 文件通过了 kernel 检查。黄色的 linter warning
是代码风格提示，不是证明失败。

然后运行最终公理审计：

```bash
lake env lean QuartetV060/AxiomAudit.lean
```

当前输出只包含：

```text
propext
Classical.choice
Quot.sound
```

这些是 Lean/mathlib 通常使用的标准逻辑公理。输出中不应出现
`sorryAx`、自定义数学公理或由 `native_decide` 产生的信任入口。

## 4. 在 VS Code 中逐步阅读

1. 用 VS Code 打开
   `bandelt-dress-quartet-lean/formalization` 文件夹；
2. 安装官方 **Lean 4** 扩展；
3. 打开任一 `.lean` 文件；
4. 将光标放在定理名或某一步 tactic 后，右侧 Infoview 会显示当前
   假设和待证目标；
5. 临时删除或改动某一步，就能看到 Lean 在哪一个逻辑接口拒绝该
   改动；不要保存这种试验性修改。

## 5. 从哪里看论文最核心的证明

### A.30 和 `f₁ ≥ 0`

打开：

```text
QuartetV060/ConcreteFourFamilies.lean
```

重点定理：

```text
auxiliaryFunctional_real_eq_scaledLedger
auxiliaryFunctional_nonnegative
```

第一个定理精确表达：

```text
f₁ = (1/4) S₁ + (1/2) S₂ + (1/2) S₃ + S₄
```

第二个定理使用四类平方的非负性推出 `f₁ ≥ 0`。

### bridge reversal 和系数所有权

依次阅读：

```text
QuartetV060/PhyloBridgeReversal.lean
QuartetV060/ConcreteBridgeLedger.lean
QuartetV060/ConcreteOccurrenceSettlement.lean
QuartetV060/ConcreteGlobalPackage.lean
QuartetV060/ConcreteBlockwisePsi.lean
```

这里验证的不是“两个固定 chart 的整个小计相等”，而是：

- reversal 把 `(K,H,L)` 变成 `(L,H,K)`；
- source occurrence 与 reversed target occurrence 由双射逐项对应；
- 对应项的系数保持；
- 整个 bridge orbit 求和后边界项抵消；
- first-face 与 second-face 的支付和重索引闭合。

### 从 `f₁` 到 quartet 数量

打开：

```text
QuartetV060/CorrectionKernel.lean
QuartetV060/TreeKernel.lean
QuartetV060/QuartetTopologyCounting.lean
QuartetV060/DistinctTupleCounting.lean
QuartetV060/MainTheorem.lean
```

其中 `QuartetTopologyCounting.lean` 明确证明 24 个位置排列对应的局部
Gram 表。它没有用 `native_decide` 把这张表交给外部编译器，而是把
六个有序不同 topology pair 的 fiber 大小和系数逐项证明出来。

### 最终渐近结论

打开：

```text
QuartetV060/Sharpness.lean
```

重点定理：

```text
normalizedMaximum_tendsto_two_thirds
```

它把 Appendix A 给出的上界和独立的随机重标号下界夹逼在一起，形式
化地得到最大 quartet distance 的归一化值趋于 `2/3`。

### Appendix B

打开：

```text
QuartetV060/DistanceCovariance.lean
```

重点定理：

```text
splitSystemDistanceCovariance_eq_detSquare
splitSystemDistanceCovariance_nonnegative
```

该文件逐步证明：

```text
double-centered split metric
  = -2 × centered indicator × centered indicator
```

以及：

```text
distance covariance
  = 4 × weighted sum of normalized split determinant squares ≥ 0.
```

## 6. 如何对应回论文

查阅：

```text
FORMALIZATION_MAP.md
```

它逐项列出正文、Appendix A 和 Appendix B 的纸面步骤及对应的 Lean
模块和定理名。阅读论文某个公式时，可以先在该表中找到对应模块，
再在 VS Code 中跳转到定理定义。

## 7. 形式化结论的准确边界

已经 kernel-check 的是：

- binary leaf-labelled phylogenetic tree 上的主定理证明链；
- Appendix A 的具体 bridge-ledger 实例；
- Appendix B 的一般有限加权 split-system 恒等式；
- 最终 `2/3` 渐近极值。

Appendix C 的 25-leaf 例子是数值说明，不参与定理证明。它所使用的
三种一般公式已经在 Lean 中证明，但论文打印的两个 Newick 树及
`9273/390625` 这一组具体数据没有另外做成 Lean 定理。审查这些具体
数字仍应运行原来的精确有理数验证程序。
