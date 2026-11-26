# 哥德巴赫逐点相关下界的阶段源码

对应研究台命题 `L-goldbach-dyadic-correlation-floor`。令 `w(k)` 在素数上取自然对数，在其余自然数上取零。记 `corr(n)` 为从 `p=0` 到 `n` 的 `w(p)w(n-p)` 之和。冻结命题要求对每个充分大的偶数给出同一个正线性下界。该命题仍开放。

| 已在 Lean 4.36 核验的结果 | 源码 |
| --- | --- |
| 存在固定 `K>0`，每个充分大的 `[X,2X)` 中，满足 `corr(n) < n/36` 的偶数至多有 `K X/(log X)^3` 个。 | [三次对数例外界](VerifiedGenuineGoldbachCubicExceptions.lean) |
| 每个充分大的偶数 `n` 都至少有 `n/(25165824 (log n)^2)` 个不同的素数 `p`，满足 `n/4 < p ≤ n/2`，且补数 `n-p` 无平方因子，素因子个数计重数至多为 7。正式声明同时给出最小素因子的筛限。 | [逐点七因子定理](VerifiedSevenFactorGoldbach.lean) · [筛集定义](VerifiedBoundedFactorBrun.lean) |
| 对每个指定的对数误差幂，真素数的等差数列前缀误差在模数总和上可达到平方根水平，模数上限含相应的对数损失。 | [半水平分布定理](VerifiedPrimeHalfDistribution.lean) |
| 对 `m=n-p` 只含一个或两个素因子且所有素因子都至少为 `z` 的候选，取权 `log p · log m`。总质量减去乘了 `(−1)^Ω(m)` 的带符号质量，等于筛限内真素数对质量的两倍。被删去的真素数对原始质量至多为 `z (log n)^2`。 | [精确恒等式及与原题的等价关系](VerifiedRoughP2ParityGap.lean) |
| 对充分大的偶数 `n` 及 `n ≤ z^11`，上述候选的双对数总质量至多为 `500 n²/φ(n)`。固定 `0<a<1/2` 后，端点指数都趋向 `a` 的素因子区间所占的质量为 `o(n²/φ(n))`。 | [总质量上界](VerifiedRoughP2SingularUpper.lean) · [移动窄区间估计](VerifiedRoughP2ExponentNoAtom.lean) |

在最后的奇偶分解中，仍须对所有充分大的偶数证明总质量与带符号质量的差至少为 `c n`。从陈氏量级的候选计数推出最终下界的接口显式要求额外的带符号估计。外部陈氏粗筛加权下界在原工具链上的整链重放未完成。有关广义黎曼猜想的辅助定理在声明中保留各自所需的假设。[计数与奇偶偏差的归约](VerifiedRoughP2WeightedTransfer.lean) · [GRH 接口](VerifiedDirichletGRHLocalBridge.lean)

## 复验

在本目录使用 `lean-toolchain` 与 `lake-manifest.json` 锁定的版本。源码包有 236 个证明模块及一个汇总入口。执行以下命令可以从源码构建并打印八条主要声明的公理依赖。

```sh
lake exe cache get
lake build GoldbachCheckpoint
lake env lean -DwarningAsError=true GoldbachCheckpoint.lean
lake env leanchecker -v VerifiedGenuineGoldbachCubicExceptions
lake env leanchecker -v VerifiedSevenFactorGoldbach
```

整理提交时，在已有的锁定依赖与已编模块上重新运行了汇总入口。八条输出均仅含 `propext`、`Classical.choice`、`Quot.sound`。若定理含有显式数学前提，公理表不会将前提列为公理，判断结论时请同时阅读定理类型。本次未另做一轮空缓存全包构建。SHA-256 清单按 UTF-8、LF 换行计算。[汇总入口](GoldbachCheckpoint.lean) · [实际公理输出](axioms.txt) · [源码校验清单](SOURCE-SHA256.txt)

## 来源

源码保留原文件的来源与署名。主弧模块选取和移植了 DFQDZZ/goldbach-proofs 固定提交 `e4ab24712555ae8c2c926adf19d368a9fb392c35` 的材料，包括 XianWu18 与 wzhxzkk 的工作。部分解析引理来自 OpenAI 的 openai/math 固定提交 `f5702854040e97fa7675c21ba37a9608f5f92dd3`。深弧矩估计另在原文件注明了 TranswarpDrive 的贡献。数学库固定在 mathlib 的 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。[上游主弧源码](https://github.com/DFQDZZ/goldbach-proofs/tree/e4ab24712555ae8c2c926adf19d368a9fb392c35) · [OpenAI 解析引理源码](https://github.com/openai/math/tree/f5702854040e97fa7675c21ba37a9608f5f92dd3) · [仓库许可证](../../../LICENSE)
