# 当前路线（2026-10-09 02:42 UTC）

最新经过核检查的范围以 STATUS.md 和各里程碑报告为准。下面旧计划中关于 abelian localization 尚未完成、scheme 阶段尚未启动的段落保留作历史记录，已被本段取代。

- 小 abelian 范畴的 dévissage 和规范 connective Serre localization 已完成，包括真实弱同伦纤维比较、所有次数的规范映射及 K₀ 尾项。
- 真实 scheme 向量丛 K、coherent G、规范 K→G、开限制函子及其自然性已建立。
- noetherian scheme 任意开浸入的 supported G 长正合列已经完成；主理想闭浸入也已有真正 G(Z) 的闭开序列。
- 任意理想的仿射闭 dévissage 与规范 Spec(PID) 的 K=G 已通过作者构建，正在独立审查与公开接口整合；非仿射闭浸入与更一般 regular 比较继续推进。
- perfect-complex K 并行开发。真实 quasi-isomorphism Waldhausen S 构造和 strict-perfect 模型已建立；所有 perfect complexes 的几何闭包、Q/S、Gillet–Waldhausen 与全局比较不提前声称完成。
- 一般 exact category 的扩展只按当前 scheme 证明需要推进。K₀ Grothendieck 比较、nonconnective 扩展及更强普通同伦等价仍单独列为后续目标。

## 历史计划

# Quillen Q-construction 形式化：路线与当前边界

这项工程在 Lean 中使用真实的 exact category、拉回、同构类商、nerve、几何实现和同伦群。通过编译的部分不含 `sorry`，也没有把目标定理写成新的公理。

## 已经检查通过的主线

1. 定义通常的 Quillen exact structure，并从公理证明 admissible 态射的基本性质。
2. Q 的箭头是 `X ← M → Y` 的同构类：左边 admissible epi，右边 admissible mono。复合用真实拉回，单位律和结合律已证明。
3. 定义 `K_n(E) = π_(n+1)(|NQ(E)|, 0)`。这里的基点来自原 exact category 的零对象，不把它错误地当作 Q 中的零对象。
4. 证明 exact functor 保持所需拉回，并给出真正的 K 群同态及恒等、复合定律。还将其打包为固定宇宙下的群值函子。
5. 构造 actual geometric realization 的 cylinder 同构，将 simplicial homotopy 转为连续同伦，并证明带基点版本。
6. 构造实际的拓扑 homotopy fiber，证明其长正合列：正次数的三类正合位置、低次数 pointed-set 尾部，以及严格交换方块下的自然性。
7. 证明代数 Grothendieck 群的 dévissage 和 Serre localization。两者都使用真实的过滤、短正合列和商范畴论证。

具体测试包含所有小的整数模所成的 abelian category，以及 `ℤ → ℤ ⊞ ℤ → ℤ` 的分裂短正合列。这个例子不是通常用有限生成投射模定义的环 `ℤ` 的 K 理论。

## 用户要求的两个最终目标

### Quillen dévissage

采用经典 abelian-category 版本：full subcategory 非空，对子对象、商对象、有限乘积封闭，而且每个 ambient 对象都有有限过滤，其各层商属于该子范畴。

这里不能额外要求子范畴对 extensions 封闭，否则结合过滤生成条件会把目标退化为整个范畴。当前小 abelian category 版本的完整 dévissage 已证明：真实 Q-comma 范畴与 layer poset 的等价、有限过滤收缩及 Theorem A 给出 classifying-space 同伦等价，并诱导所有 n ≥ 0 的 K 群同构。正向同态严格等于已有 inclusion KMap，包含零对象基点归一化。

### Quillen localization

采用 Serre 子范畴及其 abelian quotient 的经典版本。真实 quotient、exact quotient functor、K 映射、代数 Grothendieck 群的 kernel/quotient 结论均已构造。

当前还构造了基点兼容的比较映射 `BQ(Serre) → HF(BQ(quotient))`，并证明它与实际 inclusion K-map 相容、quotient 与 inclusion 的 K-map 复合为零。尚未证明这个比较映射是同伦等价，因此尚未声称完整的 Quillen localization 定理。

## 当前主要剩余证明

- Quillen Theorem B 的完整 homotopy-cartesian realization 步骤；Theorem A 已用真实 comma 类空间的可缩性证明，正向映射严格等于原 nerve realization 映射
- 完成 localization fiber theorem；小范畴版本的高阶 dévissage 已证明
- 同伦定义的 K₀ 与代数 Grothendieck 群的比较、K₀ 的交换性
- 超出当前固定宇宙/小范畴接口的运输，以及一般 Serre-pair 方块的完整基点自然性

已经证明的拓扑长正合列是一般 homotopy fiber 的定理；它本身不能替代 localization 中尚未证明的 fiber comparison 等价。

## 如何复现

先安装官方 elan，然后在项目根目录运行：

```sh
lake exe cache get
lake build
./scripts/audit.sh
```

`lean-toolchain` 和 `lake-manifest.json` 固定了 Lean/mathlib 版本。`audits/LibraryAudit.lean` 会遍历所有导入的 Quillen 声明，拒绝依赖 `propext`、`Classical.choice`、`Quot.sound` 之外的假设。最新数值与日志位置见 `STATUS.md`。

## 新增正式目标：正合范畴版本（2026-10-08 21:26 UTC）

用户明确要求继续完成 exact category 的 dévissage 与 localization。一般 exact category 的 Q 构造和 K 函子已有；新增的两个定理尚未完成。先依据原始文献固定真正有效的 admissibility、过滤、闭包及 quotient 存在条件，再实现证明。不能直接删除当前证明的 `Abelian` 假设，也不能将 nonconnective localization 的低次数结论偷换为 connective K₀ 的满射。最终映射必须连接到已有的真实 Q-based KMap。现有 abelian localization 与 K₀ 比较仍并行推进。

## 后续阶段：scheme 的 K/G-theory（2026-10-08 21:27 UTC）

按用户 2026-10-08 22:18 UTC 的最新顺序，先完成当前 abelian localization，然后直接进入 schemes 的 K/G-theory，构造并证明基本性质，包括 localization sequence。一般正合范畴的 dévissage/localization 只在 scheme 阶段需要时并行推进，不再作为前置任务；无关的 K₀ 扩展也不延迟这一顺序。区分 vector bundles、perfect complexes 与 coherent sheaves；各比较与局部化结论应明确所需的 scheme 条件和 connective/nonconnective 低次数范围。现在只记录路线，不提前启动大规模 scheme 阶段。
