## 大素数项的次弧积分可以删去哪段频率

设 **$n$** 是目标偶数。仓库给整数 $p$ 赋予权重 $h_n(p)$：若 $p$ 为素数且 $p^3>n$，权重为自然对数 $\log p$，其余取零。把主弧分母上限记为 $Q=\lfloor\log_2(n+2)\rfloor^2$。对满足 $0\le p,r\le n$ 的一对索引，它在大素数项的次弧积分中的整数频率是 $p+r-n$。（[目标命题](../../gaps.json)，[积分展开](BandPairs.lean)）

令 $L=1+\lfloor\log_2(n+2)\rfloor$，$K=\lfloor n/L^4\rfloor$。在 $n>2Q^2$ 时，主弧互不重叠。把满足 $0<|p+r-n|\le K$ 的项在次弧上的贡献之和记为 $R(n)$，则有

$$
|R(n)|\le 4\log(4)\,n\,\frac{(1+2\log L)^2}{L}.
$$

**可以从原命题中删去这一整段非零频率。** 当 $n$ 增大时，$K$ 趋于无穷，$R(n)/n$ 趋于零。保留 $p+r=n$ 和 $|p+r-n|>K$ 的项后，“对每个 $\varepsilon>0$，对所有充分大的偶数，实部至少为 $-\varepsilon n$”与登记的目标命题等价。剩余频率的下界仍待证明。（[误差界和等价定理](BandReduction.lean)）

### 证明的三个环节

1. 将互不重叠的主弧按既约分母求和。分母为一的弧在单位区间两端各占一部分，周期性将它们合成完整的一条弧。仓库已核验所需的不相交条件和截断参数最终满足该条件的事实。（[弧积分](BandGeometry.lean)，[不相交引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/153)，[尺度引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/196)）
2. 求次弧指示函数的整数傅里叶系数。按频率与分母的公因子展开拉马努金和，对一段频率求绝对值之和，得到只含两个调和和因子的平均上界。（[算术估计](BandArithmetic.lean)，[完整傅里叶系数](BandMask.lean)）
3. 固定第一个索引 $p$ 后，每个正的绝对频率至多对应两个 $r$。用切比雪夫函数控制所有素数权重的总和，再将频率平均上界代入，得到上式。（[素数对估计](BandPairs.lean)，[Mathlib 的切比雪夫上界](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Chebyshev.lean#L190)）

### 剩余高频需要控制哪个量

对整数 $k\ge0$，令 $A_n(k)$ 为满足 $|p+r-n|=k$ 的所有有序对的权重 $h_n(p)h_n(r)$ 之和，其中 $0\le p,r\le n$。对分母 $q$，记 $c_q(k)$ 为拉马努金和。令 $D_n$ 为零频贡献，即 $A_n(0)$ 乘以次弧在单位区间内的长度。对整数 $K\le t\le n$，定义**带符号的前缀和**

$$
S_n(t)=\sum_{K<k\le t}A_n(k)\sum_{q=1}^Q c_q(k)
    \sin\!\left(\frac{2\pi kQ}{qn}\right).
$$

在 $n>2Q^2$ 时，删去小频带后剩余的积分实部恰好为 $D_n-H_n$，其中

$$
H_n=\frac1\pi\left(\frac{S_n(n)}{n}
     +\sum_{K<k<n}\left(\frac1k-\frac1{k+1}\right)S_n(k)\right).
$$

因此目录中的高高项下界等价于如下估计：对每个 $\varepsilon>0$，对所有充分大的偶数 $n$，有 $H_n\le D_n+\varepsilon n$。这里的 $D_n$ 包含满足 $p+r=n$ 的实际素数对权重；用一个简单的常数替代它需要另行证明。不同位置的前缀和可以有不同的符号，此公式保留了它们各自的权重。（[频率重排、分部求和与等价定理](TailPrefixes.lean)）

### 第一段剩余频率可以怎样简化

令 $H=\lfloor n/Q\rfloor$。在第一段剩余频率 $K<k\le H$ 中，对每个分母 $q$ 定义角度 $x_{q,k}=2\pi kQ/(qn)$。这段频率使用的精确系数包含 $\sin(x_{q,k})/(\pi k)$。当 $q\le L$ 时保留它，当 $L<q\le Q$ 时用 $x_{q,k}/(\pi k)=2Q/(qn)$ 替代。把第一段带符号加权和在替代前后的差记为 $E_n$。对每个 $n\ge 1$ 都有

$$
|E_n|\le \frac{4\log(4)(2\pi)^2}{6}\,n\,
          \frac{(1+2\log L)^2}{L}.
$$

这个上界对第一段的下端点一致成立。因为 $kQ\le n$，有 $0\le x_{q,k}\le 2\pi/q$。在大分母上使用三次余项 $|\sin x-x|\le |x|^3/6$，再对拉马努金和取频率平均，就能保留公式中的 $L^{-1}$ 衰减。特别地，$E_n/n$ 趋于零。高于 $H$ 的频率仍使用精确系数，零频贡献仍为 $D_n$。用这个替代后的总损失去比较 $D_n+\varepsilon n$，与原来的逐偶数下界等价。（[有限误差界与等价定理](FirstBand.lean)）

对正整数 $d$，令 $M_d$ 为第一段中满足 $d\mid k$ 的 $A_n(k)$ 之和，记 $\mu$ 为莫比乌斯函数。大分母的替代项可以精确写成

$$
\sum_{L<q\le Q}\frac{2Q}{qn}\sum_{d\mid q}d\,\mu(q/d)\,M_d.
$$

因为 $k=|p+r-n|$，$M_d$ 只统计满足 $p+r\equiv n\pmod d$ 且落在该频段的有序素数对。这个表达式给出了可以直接研究的算术量；小分母的正弦项、较高频率的贡献及其与零频之间的比较仍须控制。（[整除条件恒等式](FirstBand.lean)）

### 扣除各余数类的均值

在第一段频率 $K<k\le H$ 中选正整数周期 $P\le L$。对每个余数 $r$，令 $b_r$ 为该段内所有满足 $k\equiv r\pmod P$ 的 $A_n(k)$ 的平均值，空类取零。定义偏差 $U_n(k)=A_n(k)-b_{k\bmod P}$。对每个正因子 $d\mid P$，

$$
\sum_{\substack{K<k\le H\\ d\mid k}} U_n(k)=0.
$$

因为 $d\mid k$ 选中的是模 $P$ 的若干完整余数类，而每一类的偏差之和都等于零。因此对分母 $q$ 展开拉马努金和时，只需保留满足 $d\mid q$ 且 $d\nmid P$ 的除数。偶数目标 $n\ge8$ 的奇频率质量为零，取 $P=2$ 时扣除的正是偶频率的共同均值。（[奇频率支撑与除数消去定理](PeriodicMass.lean)）

记 $V_n$ 为上一节线性化后的总损失。仅在大分母 $L<q\le Q$、第一段频率 $K<k\le H$ 的线性项中用 $U_n(k)$ 替换 $A_n(k)$，所得总损失记为 $V_{n,P}$。对每个 $n\ge2$ 有

$$
|V_n-V_{n,P}|\le 4\log(4)\,L^8.
$$

这个上界除以 $n$ 后趋于零，且对上述所有周期一致。证明利用了一个完整周期内的抵消：当 $q\nmid P$ 时，沿任何步长为 $P$ 的等差数列连续取 $q$ 项，其拉马努金和的总和等于零。有限频段只留下不完整周期的边界贡献，因而小样本中的均值贡献仍可很大。即使随 $n$ 改变周期，原高高项目标仍等价于对每个 $\varepsilon>0$ 和充分大的偶数 $n$ 证明 $V_{n,P}\le D_n+\varepsilon n$。仍需估计类内偏差与剩余除数的相关性，并控制小分母和较高频率的项。（[均值误差与原目标的等价定理](PeriodicMass.lean)）

还可以用同一个周期选择规则消去任意预先给定的有限组除数。令 $j$ 为满足 $j!\le L$ 的最大整数，取 $P=j!$。随着 $n$ 增大，$j$ 趋于无穷。任选固定上限 $D$，对所有充分大的 $n$，每个 $1\le d\le D$ 都整除 $P$，因此这部分偏差贡献同时严格为零。这里的除数是拉马努金和展开中的 $d$；小分母的原始正弦项仍保留在等价命题中。（[增长周期与统一消去](PeriodicMass.lean)）

### 第一段大分母项需要多小的素数对波动

设 $B,Q$ 是非负整数，$\varphi(q)$ 是 $1$ 到 $q$ 之间与 $q$ 互素的整数个数。对偏移量 $k$，定义**大分母权重** $F_{B,Q}(k)$ 和**对角和** $J_{B,Q}$ 为

$$
F_{B,Q}(k)=\sum_{B<q\le Q}\frac{c_q(k)}q,\qquad
J_{B,Q}=\sum_{B<q\le Q}\frac{\varphi(q)}{q^2}.
$$

对任意非负整数端点 $K,H$，令 $T=\max(H-K,0)$ 为窗口内的整数个数。按分母展开平方后，不同分母的交叉项在完整公共周期内相消，每个分母 $q$ 的平方项在一个周期内平均为 $\varphi(q)$（这里指 $c_q(k)^2$）。对窗口两端余下的项求和，得到**有限窗口平方和估计**

$$
\left|\sum_{K<k\le H} F_{B,Q}(k)^2-TJ_{B,Q}\right|\le Q^4.
$$

取项目的 $B=L$ 及前文定义的 $Q,K,H$ 时，$Q^4/T$ 随 $n$ 增大趋于零。因此每个偏移量上的平均平方与 $J_{L,Q}$ 的差趋于零，即使 $J_{L,Q}$ 本身随 $n$ 改变。这个结论仅使用拉马努金和的性质和项目的窗口长度。（[有限估计及窗口上的渐近式](RamanujanEnergy.lean)）

允许周期 $P$ 随 $n$ 变化，且 $1\le P\le L$。用前节的类内偏差 $U_n(k)$ 定义**偏差平方和** $W_n=\sum_{K<k\le H}U_n(k)^2$。中心化后的大分母项是 $(2Q/n)\sum_{K<k\le H}U_n(k)F_{L,Q}(k)$。对这个内积使用柯西–施瓦茨不等式，得到使大分母项除以 $n$ 后趋于零的一个充分条件，即沿全体偶数 $n\to\infty$ 有

$$
\frac{Q(1+J_{L,Q})}{n^3}\,W_n\longrightarrow 0.
$$

**待证的是素数对的波动估计。** 如果这个条件成立，原高高项下界就等价于只对小分母项与更高频率项之和证明前文的单侧上界。该单侧上界仍是独立的待证步骤。（[柯西–施瓦茨估计和条件等价定理](RamanujanEnergy.lean)）

### 怎样使用经典的哥德巴赫加权计数

对非负整数 $m$，令 $r_2(m)$ 为所有满足 $p+r=m$ 的有序素数对的 $\log p\log r$ 权重之和。项目还要求两个素数都不超过 $n$，且各自的立方都大于 $n$。对 $1\le k\le n$，令 $E_n(k)=r_2(n-k)+r_2(n+k)-A_n(k)$，并令 $a=\lfloor\sqrt[3]{n}\rfloor$。两个目标和在 $k>0$ 时互异，有**有限截断误差界**

$$
0\le E_n(k)\le 2\log(4)\,[a+\max(a,k)]\,\log(2n).
$$

对目标和 $n-k$，每一对被剔除的素数至少有一个不超过 $a$。对目标和 $n+k$，如果一个素数超过 $n$，另一个必小于 $k$。因此被剔除的素数对至少有一个坐标不超过 $\max(a,k)$。固定这个坐标就决定了另一个坐标，对较小坐标的对数权重使用切比雪夫上界就得到上式。$k=0$ 的零频贡献仍使用原有定义。（[有限截断定理](GoldbachTruncation.lean)）

在项目的窗口 $K<k\le H$ 中，**截断只消耗趋于零的方差预算**。沿所有正整数 $n\to\infty$ 有

$$
\frac{Q(1+J_{L,Q})}{n^3}\sum_{K<k\le H} E_n(k)^2\longrightarrow 0.
$$

因此可以直接为经典计数选择周期 $1\le P\le L$ 和余数类预测值 $b_n(r)$。若沿所有充分大的偶数，将上式中的 $E_n(k)$ 替换为 $r_2(n-k)+r_2(n+k)-b_n(k\bmod P)$ 后仍趋于零，则第一段的大分母项是 $o(n)$。这里利用了各余数类均值使类内平方误差最小。经典的二元哥德巴赫均方定理给出 $r_2$ 与含奇异级数的主项之间的均方误差估计。该主项所需的周期近似和两侧平移误差见下文。较高频率和小分母项仍须满足前文的单侧界。（[方差预算及条件等价定理](GoldbachTruncation.lean)，[Vaughan 课程讲义，定理 8](https://personal.science.psu.edu/rcv4/571s25/Class571-07.pdf)）

### 小素数能把奇异级数逼近到什么精度

对正整数 $m$ 和整数截点 $y\ge2$，定义**截断的奇异级数因子** $s_y(m)$。若 $m$ 为奇数，取零。若 $m$ 为偶数，取

$$
s_y(m)=\prod_{\substack{3\le p\le y\\p\text{ 为素数},\ p\mid m}}
\left(1+\frac{1}{p-2}\right).
$$

令 $s(m)=s_m(m)$。乘回与 $m$ 无关的常数 $2C_2$ 就得到经典二元奇异级数，其中 $C_2=\prod_{p>2}(1-1/(p-1)^2)$，乘积遍历奇素数。因为每个保留的素数以及 $2$ 都整除 $y!$，$s_y(m)$ 只依赖于 $m$ 除以 $y!$ 的余数。（[周期性证明](SingularSeriesWindow.lean)，[Vaughan，定理 8 的欧拉乘积](https://personal.science.psu.edu/rcv4/571s25/Class571-07.pdf#page=101)）

对任意整数 $0\le K\le H$，记 $h(H)=\sum_{1\le d\le H}1/d$，空和取零。取绝对常数 $C=e^9(9e^9+9e^{18})$。对整个窗口有**无条件的均方界**

$$
\sum_{K<m\le H}\bigl(s(m)-s_y(m)\bigr)^2
\le C\,\frac{H-K}{y^2}+4h(H)^4.
$$

第一项的常数与窗口位置、上端点及截点均无关。平方展开后，一对除数同时整除 $m$ 的频率由它们的最小公倍数决定。把共同的大素因子和只出现在一侧的大素因子都计算在内，得到 $y^{-2}$ 衰减。有限窗口中每个最小公倍数的计数误差至多为一；用仓库已有的除数调和和估计汇总这些误差，得到第二项。（[欧拉乘积尾界](SingularSeriesFactors.lean)，[最小公倍数与欧拉因子](SingularSeriesDivisors.lean)，[整数窗口定理](SingularSeriesWindow.lean)）

### 用一个经典均方定理控制第一段的大分母项

令 $c$ 为实数常数。假设存在与正整数 $X$ 无关的常数 $A\ge0$，使所有充分大的 $X$ 满足

$$
\left(\sum_{m=1}^X [r_2(m)-c\,m\,s(m)]^2\right)(\log X)^4\le A X^3.
$$

对经典归一化 $c=2C_2$，这个假设对应 Vaughan 定理 8 中取对数指数为 $4$ 的情形。**在这个单一假设下，第一段中心化后的大分母项除以 $n$ 趋于零。** Lean 定理的假设中不需要给各个余数类另行指定素数对分布估计。经典均方定理本身以显式前提出现。（[均方假设和大分母项定理](SingularSeriesTransfer.lean)，[Vaughan 的定理陈述](https://personal.science.psu.edu/rcv4/571s25/Class571-07.pdf#page=101)）

具体取 $y$ 为满足 $y!\le L$ 的最大整数，按周期 $y!$ 用 $c\,n[s_y(n-k)+s_y(n+k)]$ 预测双侧计数。两侧的经典计数误差由 $X=2n$ 的全区间均方界控制。把主项中的 $n\pm k$ 换成 $n$ 会带来因子 $k$，但窗口上有 $k\le n/Q$。大素因子的尾部则需支付与 $(1+J_{L,Q})/y^2$ 成正比的误差；由于 $L<(y+1)!$，这个比值趋于零。用这些估计和截断定理可得，在相同文献前提下，登记的高高项下界等价于只估计小分母与更高频率的带符号之和，并与实际零频贡献比较。后一个单侧不等式仍待证明。（[双侧有限估计、阶乘尺度与最终等价定理](SingularSeriesTransfer.lean)）

### 第一段只保留周期的约数

沿用上文的窗口端点 $K,H$、分母上限 $Q$ 和阶乘周期 $P=y!$。记 $A_n(k)$ 为偏移量 $k$ 的真实高段素数对权重，$M_n(k)$ 为全部分母的精确主弧系数。对 $K<k\le H$，令 $b_n(k)=cn[s_y(n-k)+s_y(n+k)]$。在上述经典均方假设下，**第一段所有真实权重可以同时换成这个显式周期函数**。对每个充分大的偶数 $n$，替换带来的总误差满足

$$
\left|\sum_{K<k\le H}(A_n(k)-b_n(k))M_n(k)\right|=o(n).
$$

这里的小量对同一阈值以上的所有偶数成立。证明保留原始正弦系数，在 $kQ\le n$ 上用三阶余项控制它与线性核之间的差，再用柯西–施瓦茨不等式将核的平方和与素数对的均方误差配对。分母 $q=1$ 也在求和中。（[精确核、平方和与替换误差](ExactFirstBand.lean)）

令 $R_n$ 为周期模型中只对满足 $1\le q\le Q$ 且 $q\mid P$ 的分母求和所得的第一段贡献，每个保留项仍取原始正弦权重。对**任意正整数** $n$，全部分母的周期模型与 $R_n$ 的差满足

$$
\left|\sum_{K<k\le H} b_n(k)M_n(k)-R_n\right|
\le 20|c|L^9.
$$

这一步是无条件的。对 $q\nmid P$，周期权重乘以拉马努金和的每个完整块之和为零。对不完整块使用分部求和，控制相邻正弦权重之差，并保留最右端的边界项。由于 $L$ 随 $n$ 只按对数增长，上界除以 $n$ 趋于零。（[有限误差界及条件等价式](NonresonantBand.lean)）

因此，在经典均方假设下，原高高项下界等价于以下单侧比较：将 $k>H$ 的真实带符号贡献与 $R_n$ 相加，所得结果至多为真实零频贡献加 $o(n)$。这一步保留了零频的真实素数对计数。剩余约数项的大小和更高频率的单侧控制仍需研究。（[outer_resonant_iff](NonresonantBand.lean)）

### 第一段贡献的显式公式

令 $n$ 为目标偶数，$L=1+\lfloor\log_2(n+2)\rfloor$，$Q=(L-1)^2$。取满足 $y!\le L$ 的最大整数 $y$，记 $P=y!$。对正整数 $q$，令 $c_q(n)$ 为拉马努金和，$\varphi(q)$ 为欧拉函数。定义正弦积分 $\operatorname{Si}(x)=\int_0^x (\sin t)/t\,dt$，被积函数在零点取连续延拓值 $1$。沿用经典均方假设中的归一化常数 $c$，定义

$$
E_n=c\,n
\prod_{\substack{3\le p\le y\\ p\text{ 为素数}}}
\left(1+\frac{1}{p(p-2)}\right)
\sum_{\substack{1\le q\le Q,\ q\mid P\\ q\text{ 无平方素因子}}}
\frac{c_q(n)}{\varphi(q)^2}\,\frac{\operatorname{Si}(2\pi/q)}{\pi}.
$$

**在同一个经典均方假设下，真实第一频段贡献与 $E_n$ 的差为 $o(n)$。** 公式只需目标偶数、有限个小素数和正弦积分。例如，$4\mid P$ 时，分母 $4$ 的算术权重在完整周期上的平均严格为零。在实际窗口上，它仍可能产生边界误差。证明先对每个分母控制这个误差，再求和。（[完整周期的算术平均](ResonantMean.lean)，[实际窗口的误差](AveragedBand.lean)，[欧拉乘积公式](ConductorEuler.lean)）

正负偏移量各贡献一次。每个奇素数 $p\mid q$ 使平均系数多出一个 $1/(p-1)^2$ 因子，素数 $2$ 对应的因子恰为 $1$。对网格上的正弦权重求和时，去掉开头的小窗口、上端点的取整以及网格近似均产生误差。三者在实际截断尺度上合计为 $o(n)$。（[双侧整周期恒等式](ResonantMean.lean)，[分母系数的精确分解](ConductorEuler.lean)，[正弦积分的两个端点](FirstBandSineIntegral.lean)）

令 $O_n$ 为偏移量 $k>\lfloor n/Q\rfloor$ 的真实贡献，令 $D_n$ 为原问题的真实零频贡献。剩余任务是证明对任意 $\varepsilon>0$，每个充分大的偶数都满足 $O_n+E_n\le D_n+\varepsilon n$。在经典均方假设下，这条不等式与登记的高高项下界等价。（[冻结目标的等价定理](ConductorEuler.lean)）

### 阶乘目标上，第一段有严格正的线性主项

取文献中的归一化 $c=2C_2$。对整数 $m\ge0$，定义只依赖于各个同余类的函数

$$
F(m)=\sum_{\substack{q\ge1\\q\text{ 无平方素因子}}}
\frac{c_q(m)}{\varphi(q)^2}\,\frac{\operatorname{Si}(2\pi/q)}{\pi}.
$$

这个级数对所有 $m$ 一致绝对收敛。原因是 $|c_q(m)|\le\varphi(q)$，无平方素因子的分母满足 $q\le 2\varphi(q)^2$，而 $|\operatorname{Si}(2\pi/q)|/\pi\le2/q$。所以每项绝对值都至多为 $4/q^{3/2}$。随着截点增长，每个固定分母最终进入阶乘周期。有限欧拉乘积的归一化因子也与截断的孪生素数常数逐项相消。（[一致收敛与归一化](InfiniteBand.lean)，[与 Vaughan 原式的对接](VaughanAlignment.lean)）

记 $B_n$ 为窗口 $K<k\le H$ 内真实的第一段带符号贡献。在前述经典均方假设下，当 $n$ 沿偶数趋于无穷时有 $B_n=2nF(n)+o(n)$。因而也可以用 $2nF(n)$ 代替上文单侧比较中的 $E_n$。此式保留了第一段对目标数同余类的依赖。（[真实频段误差与原命题的等价式](InfiniteBand.lean)）

**第一段不能整体计入次线性误差。** 令 $j$ 为趋于无穷的正整数，取目标为 $j!$。对每个固定 $q$，当 $j\ge q$ 时有 $q\mid j!$，于是 $c_q(j!)=\varphi(q)$。由一致可和的上界可以逐项取极限，得到

$$
\lim_{j\to\infty}\frac{B_{j!}}{j!}=2F(0)>0.
$$

这里的 $0$ 指各个分母下的零余数。级数在这个余数上的各项均为正，分母 $1$ 的一项已给出严格正的下界。该结论说明，要检验逐偶数的下界，必须计入这段贡献。更高频率与真实零频之间的单侧比较仍然开放。（[阶乘子列极限](InfiniteBand.lean)，[正弦积分的正性](FirstBandSineIntegral.lean)）

### From the major arcs to the ordinary Goldbach count

For a positive target integer $n$, write $Q=\lfloor\log_2(n+2)\rfloor^2$. Let $R(n)$ denote the sum of $(\log p)(\log r)$ over ordered prime pairs $(p,r)$ satisfying $p+r=n$. For a denominator $q$, let $c_q(n)$ be the Ramanujan sum, $\mu(q)$ the Möbius function and $\varphi(q)$ Euler's totient. For $z\ge 0$ define

$$
J(z)=\int_{-z}^{z}\left(\frac{\sin(\pi t)}{\pi t}\right)^2\,dt,
\qquad
M(n)=n\sum_{1\le q\le Q}c_q(n)\frac{\mu(q)^2}{\varphi(q)^2}J(Q/q).
$$

The integrand takes the value $1$ at $t=0$. The argument $Q/q$ comes from the actual half-width $Q/(qn)$ of each arc. Summing its centre phase over the reduced numerators gives $c_q(n)$. The arcs at the endpoints of the unit interval together contribute one complete arc. ([Finite major-arc integral](OuterArcModel.lean))

**External input.** Vaughan's Theorem 5 with exponent $3$ supplies the uniform estimate for the full log-weighted prime exponential sum. The proof below takes that theorem as a hypothesis. It verifies the actual range of denominators and offsets, the removal of primes satisfying $p^3\le n$, and the replacement of the discrete exponential sum by its continuous integral. For all sufficiently large $n$, the complex major-arc integral of the high-prime spectrum differs from $M(n)$ by at most $18n/\log n$. The cutoff beyond which this holds depends on the constants in the external theorem. ([Vaughan, Chapter 7, Theorem 5, p. 69](https://personal.science.psu.edu/rcv4/571s25/Class571-07.pdf#page=69), [Lean statement and estimate](VaughanMajor.lean))

**What remains.** Under that single input, the catalogue's signed minor-arc lower bound for the high-prime spectrum is equivalent to the following assertion. For every $\varepsilon>0$ and every sufficiently large even $n$,

$$
R(n)\ge M(n)-\varepsilon n.
$$

On the entire unit circle, integration selects exactly the pairs with $p+r=n$. Restoring the omitted small primes changes this diagonal count by at most $2(\log 4)n^{1/3}\log n$. The pointwise lower bound on $R(n)$ in the display remains open in this argument. ([Diagonal truncation](GoldbachTruncation.lean), [equivalence with the frozen catalogue statement](MajorPairFloor.lean))

### A finite lower bound for every even target

For every even target $n$ and every integer cutoff $Q\ge1$, the finite model sum divided by $n$ is at least $J(1)/2>0$ (with $n>0$ for this normalization). Here is where evenness matters. Separate the primes dividing $n$ from those which do not. Each prime $p$ in the second group is odd and contributes a negative local factor of magnitude $1/(p-1)^2$. The integral weight decreases as the denominator increases. For any fixed subset of the first group, the combined loss from nonempty subsets of the second group is therefore at most one half of the empty-subset contribution. The bound follows from

$$
\prod_{j=1}^{k}\left(1+\frac{1}{(2j)^2}\right)
\le \frac{3k+2}{2k+2} \le \frac32 \qquad (k\ge0).
$$

As a consequence, Vaughan's Theorem 5 implies the catalogue's full-prime major-arc floor with constant $J(1)/4$. The checker takes the major-arc target verbatim from the catalogue and typechecks the implication. If the frozen high-prime minor-arc floor is also assumed, the ordinary Goldbach count becomes strictly positive for every sufficiently large even target. ([Finite positivity, major-arc floor and eventual representation](MajorPositivity.lean), [catalogue type check](check.py))

[Upstream PR #316](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/316) by DFQDZZ supplies a separate formal proof of the major-arc floor via Siegel–Walfisz and a discrete kernel. Its proof uses a one-third denominator-one bound. The half-mass estimate above applies to the continuous model and its finite cutoffs.

### Discharging the analytic input for the count equivalence

The proof of the count equivalence also runs using the checked source from DFQDZZ's [PR #316, fixed revision](https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean). The checker verifies the source digest, compiles it with the pinned Mathlib and imports its intermediate estimates. In particular, the prefix-error estimate, its logarithmic decay, and the rational-arc perturbation estimate suffice on the catalogue's actual arcs. Its discrete kernel includes the endpoint zero. Removing that endpoint costs at most one in the normalized exponential sum.

Consequently the equivalence between the frozen high-prime floor and $M(n)\le R(n)+\varepsilon n$ has **no external analytic hypothesis**. The high-prime floor alone then implies a two-prime representation for every sufficiently large even integer. Whether the high-prime floor itself holds remains open here. The earlier formulation using Vaughan's Theorem 5 is an alternative proof with an explicit literature input. ([Bridge from the pinned prime-sum estimates](DeskPrimeInput.lean), [finite lower bound](MajorPositivity.lean))

### Growth on multiples of a fixed factorial

Let $B$ be any real number. There are integers $k\ge2$ and $N\ge1$ such that every multiple $n$ of $k!$ with $n\ge N$ satisfies $M(n)/n\ge B$. In particular, $M(j!)/j!$ tends to infinity as the integer $j$ grows. This conclusion uses the actual cutoff and integration widths of the catalogue model. ([Factorial and progression theorems](MajorModelGrowth.lean))

To see why, let $P$ be any set of primes dividing an even target $n$ with each prime at most the cutoff $Q$. The finite lower bound above retains the empty set of prime divisors. Retaining the one-element sets $\{p\}$ for $p\in P$ instead gives a lower bound of $(J(1)/2)\sum_{p\in P}1/p$ for the normalized model at cutoff $Q$. Each such set retains at least half its contribution after accounting for the primes that do not divide $n$. The prime reciprocal sum diverges, so one can choose $P$ large enough to reach $B$ and then choose $k$ at least as large as every prime in $P$. Once the cutoff reaches $k$, the estimate applies to every multiple of $k!$. ([Finite bound for selected prime divisors](MajorPositivity.lean), [Mathlib proof of divergence](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/SumPrimeReciprocals.lean#L101-L104))

The certified major-arc approximation transfers the factorial limit to the real part of the high-prime major-arc integral divided by the target. For the ordered log-weighted **prime-pair count**, the same limit follows **if the frozen signed minor-arc floor holds**. A lower bound of the form $R(n)\ge c n$ for a fixed constant $c$ alone would leave a growing gap to the required model bound on factorials. ([Integral and conditional count theorems](MajorModelGrowth.lean))

### The actual pair count on multiples of a fixed modulus

Fix an integer $q\ge1$. Write $\varphi(q)$ for Euler's totient and $S_q(X)$ for the sum of $R(n)$ over nonnegative multiples of $q$ strictly below the integer $X$. Then

$$
\lim_{X\to\infty}\frac{S_q(X)}{X^2}=\frac{1}{2\varphi(q)}.
$$

The ordered-pair convention matters here. For each first prime $p<X$, the partner lies below $X-p$ in residue class $-p\pmod q$. Summing its log-weight over that prefix counts every ordered pair exactly once. Suppose all residue-class prefix masses up to $X$ differ from their main terms by at most $E$, where the main term for a prefix of length $m$ is $m/\varphi(q)$ in a reduced class and zero otherwise. The resulting error in $S_q(X)$ from $X(X+1)/(2\varphi(q))$ is at most $(1+\log 4)XE$. The fixed-modulus estimate from the pinned prime-progression theorem gives $E=o(X)$. No minor-arc hypothesis is needed. ([Finite identity, error estimate and asymptotic](ProgressionMean.lean), [prime-progression input from PR #316](https://github.com/DFQDZZ/goldbach-proofs/blob/e4ab24712555ae8c2c926adf19d368a9fb392c35/lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean#L4241))

For positive integers $j$, the corresponding weighted mean on $qj\le n<2qj$ tends to $q/\varphi(q)$. Its numerator sums $R(n)$, and its denominator sums the same multiples $n$. This leaves open the error at any particular target, including $n=j!$. ([Dyadic mean](ProgressionMean.lean))

The numerical comparison uses the window $X/2<n\le X$ and the same denominator for the actual count and the catalogue model. Each reported window is recomputed two ways. For $R$, the second method sums the complementary prime prefixes directly. For $M$, it groups progression targets by their residue modulo each squarefree denominator and evaluates the Ramanujan sum by the gcd formula. Numerical quadrature separately checks the normalization of the integral weight. ([Reproduction script](progression_means.py))

| Upper endpoint $X$ | Modulus $q$ | Targets | $\sum R/\sum n$ | $\sum M/\sum n$ | Difference |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16,384 | 720 | 11 | 3.69968244 | 3.76974860 | −0.07006616 |
| 131,072 | 720 | 91 | 3.71714161 | 3.74336493 | −0.02622332 |
| 1,048,576 | 720 | 728 | 3.74064648 | 3.74545764 | −0.00481116 |
| 4,194,304 | 720 | 2,913 | 3.74517663 | 3.74611516 | −0.00093854 |
| 4,194,304 | 5,040 | 416 | 4.36845870 | 4.36617883 | +0.00227988 |

With NumPy and SciPy installed, run the following from the repository root to reproduce the table and the other moduli at the same scales.

```sh
python3 research/reference-proofs/prime-band/progression_means.py --powers 14 17 20 22 --moduli 2 6 24 120 720 5040
```

### Mean error for the actual catalogue arcs

Fix an integer $d\ge1$. For each positive integer $j$, let $T_j$ be the multiples of $d$ in $[dj,2dj)$ and let $W_j=\sum_{n\in T_j} n$. Write $I(n)$ for the real part of the frozen minor-arc integral with both inputs equal to the catalogue's high-prime weight. With the integration radius and the target-dependent cutoff from the catalogue, the three limits are

$$
\frac{1}{W_j}\sum_{n\in T_j}M(n)\longrightarrow\frac{d}{\varphi(d)},
\qquad
\frac{1}{W_j}\sum_{n\in T_j}\bigl(R(n)-M(n)\bigr)\longrightarrow 0,
\qquad
\frac{1}{W_j}\sum_{n\in T_j}I(n)\longrightarrow 0.
$$

The kernel normalization follows from Parseval on the unit interval. For real $x$, the squared Fourier coefficients of a unit-modulus exponential sum to one. Integrating that identity in $x$ over a unit interval gives $\int_{\mathbb R}\operatorname{sinc}^2(\pi x)\,dx=1$, with $\operatorname{sinc}(t)=\sin(t)/t$ and $\operatorname{sinc}(0)=1$. Thus the mass $J(z)$ of the symmetric interval $[-z,z]$ tends to one as $z$ increases. ([Integral normalization](ArcMassNormalization.lean))

For an integer denominator $q$ dividing $d$, the Ramanujan sum is constant on the progression. The sum of these limiting coefficients is exactly $d/\varphi(d)$. When $q$ does not divide $d$, every complete period sums to zero. Each incomplete prefix has magnitude at most $q^2$. For fixed $q$, the factor consisting of the target times the retained integral mass is nonnegative and increasing, including where $q$ first enters the cutoff. Summation by parts therefore controls its contribution across changes of cutoff. With $X=2dj$ and $Q$ the catalogue cutoff at $X$, the combined nondividing-denominator error is at most $2XQ^3$, which is $o(W_j)$ for fixed $d$. ([Period and coefficient estimates](ProgressionConductors.lean), [moving-cutoff error and mean limits](ModelProgressionMean.lean))

The third limit uses the certified major-arc approximation and the error from removing the small primes. All three are signed averages. A sparse sequence of targets with a large negative minor-arc integral would be compatible with them. The catalogue's lower bound at every sufficiently large even target remains open. ([Transfer to the frozen integral](ModelProgressionMean.lean))

**A consequence for individual targets.** Fix $d\ge1$ and a tolerance $\varepsilon>0$. Every sufficiently large window $T_j$ contains a single target $n$ satisfying both $I(n)\ge-\varepsilon n$ and $R(n)\ge M(n)-\varepsilon n$. If all the integrals in the window fell below $-\varepsilon n/2$, their weighted mean would stay below $-\varepsilon/2$. The pointwise approximation transfers the resulting witness to the count bound with the remaining half of the tolerance. Moreover, for any real $B$, one can choose a fixed factorial modulus $d=k!$, with $k\ge2$, so that every sufficiently large window contains an even witness with $R(n)\ge Bn$ as well as the requested integral bound. The factorial determines the progression. Its multiples supply the witnesses. ([Witnesses and quantifiers](ProgressionWitness.lean))

### Shortfalls and exceptional targets

Fix a positive modulus $d$ and use the same window $T_j$ and total target weight $W_j$ as above. For each target $n$, define its downward error $D(n)=\max\{M(n)-R(n),0\}$. For a fixed threshold $\varepsilon>0$, let $P_j(\varepsilon)$ be the fraction of the $j$ targets in $T_j$ with $D(n)>\varepsilon n$. Then the following four assertions are **equivalent**.

1. The mean shortfall $\sum_{n\in T_j}D(n)/W_j$ tends to zero.
2. For every fixed $\varepsilon>0$, the exceptional fraction $P_j(\varepsilon)$ tends to zero.
3. The mean absolute error $\sum_{n\in T_j}|R(n)-M(n)|/W_j$ tends to zero.
4. The mean negative part of the frozen integral, $\sum_{n\in T_j}\max\{-I(n),0\}/W_j$, tends to zero.

The equivalences are proved unconditionally. All four limits hold by the unconditional count estimate proved below. The first implication to exceptional fractions is Markov's inequality. For its converse we proved a **uniform second-moment bound on the normalized shortfall**. There is a constant $C_d>0$ such that, for all sufficiently large $j$,

$$
\frac1j\sum_{n\in T_j}\left(\frac{D(n)}n\right)^2\le C_d.
$$

Since $R(n)\ge0$, only an upper bound for the model is needed for this estimate. The complete product over the absolute local factors bounds $|M(n)|/n$ by three times the normalized binary singular-series shape at $2n$. The existing second-moment bound for that shape then applies to even and odd targets. Cauchy–Schwarz bounds the exceptional contribution to the unweighted mean of $D(n)/n$ by $\sqrt{C_d P_j(\varepsilon)}$. Each remaining term is at most $\varepsilon$. The weights $n$ vary by a factor of at most two on the window. For assertion 3, the exact identity $|R-M|=(R-M)+2D$ uses the signed mean proved above. For assertion 4, taking the negative part changes differences by at most their original magnitude. ([Model majorant and second moment](ShortfallEnergy.lean), [four equivalent criteria](ShortfallDensity.lean))

**Reduction using the classical input.** Let $S(n)$ denote the normalized binary singular-series shape defined in the reference proof, and let $c$ be the constant in the repository's explicit hypothesis `ClassicalMeanSquare c`. Under that hypothesis, $\sum_{n\in T_j}|R(n)-cnS(n)|/W_j\to0$. Cauchy–Schwarz gives this directly from the stated logarithmic saving. The triangle inequality in both directions then makes assertion 2 equivalent to $\sum_{n\in T_j}|M(n)-cnS(n)|/W_j\to0$. This last expression compares two explicit arithmetic models. The reduction retains `ClassicalMeanSquare c` as a hypothesis. ([Exact classical input](SingularSeriesTransfer.lean), [transfer to the catalogue model](ShortfallTransfer.lean))

The optional shortfall diagnostic measures these quantities target by target. Here $d=2$, $j=\lfloor X/(2d)\rfloor$, and the threshold is $0.02n$. The two means divide by $W_j$ and the fraction divides by $j$. The observations are finite numerical measurements. ([Reproduction script](progression_means.py))

| Scale $X$ | Targets | Targets above threshold | Fraction | Mean shortfall | Mean absolute error |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16,384 | 4,096 | 2,579 | 62.96% | 0.05121850 | 0.06067887 |
| 131,072 | 32,768 | 13,668 | 41.71% | 0.02042672 | 0.02692212 |
| 1,048,576 | 262,144 | 36,192 | 13.81% | 0.00801253 | 0.01194450 |
| 4,194,304 | 1,048,576 | 23,887 | 2.28% | 0.00443914 | 0.00712387 |

```sh
python3 research/reference-proofs/prime-band/progression_means.py --powers 12 14 17 20 22 --moduli 2 720 --shortfall 0.02
```

For scales through 4,096, the script checks every target by a direct prime-pair sum and an independent gcd formula for the model. At larger scales it checks the two endpoints, both extreme errors, and the targets nearest the threshold and zero. The output reports how many computed normalized deficits lie within $10^{-10}$ of the threshold. That count is zero in each row above.

### Mean absolute agreement with the classical singular series

Let $C_2$ be the twin-prime constant and $S(n)$ the normalized binary singular-series shape. For any fixed positive modulus $d$, take the window $T_j$ and weight $W_j$ defined above. The finite catalogue model satisfies

$$
\lim_{j\to\infty}\frac{1}{W_j}\sum_{n\in T_j}
  \big|M(n)-2C_2 n S(n)\big|=0.
$$

This arithmetic comparison is **unconditional**. By the triangle inequality, the exceptional count fraction tends to zero at every fixed positive tolerance exactly when the weighted mean absolute error between the true count and the classical main term tends to zero. This equivalence requires no convergence rate. The explicit hypothesis `ClassicalMeanSquare (2*twinPrimeConstant)` suffices for that criterion. Under the same hypothesis the proportion of targets where the original frozen minor-arc integral falls below $-\varepsilon n$ also tends to zero for each fixed $\varepsilon>0$. The catalogue still asks for a lower bound for every sufficiently large even target. ([Model comparison and conditional density theorem](ModelAbsoluteMean.lean))

**Uniform control of large denominators.** For a positive integer $q$, let $\tau(q)$ count its positive divisors and put $b_q=\tau(q)\mu(q)^2/\varphi(q)^2$. In the divisor formula for the Ramanujan sum, each divisor $a$ contributes in absolute value at most $a$ on its multiples. Up to a positive integer $X$ this costs at most $a\lfloor X/a\rfloor\le X$. Thus $\sum_{1\le n\le X}|c_q(n)|\le X\tau(q)$. For squarefree $q$, the quantity $b_q$ factors as the product of $2/(p-1)^2$ over primes $p$ dividing $q$. For other $q$ it vanishes. The local weights are summable, which gives $\sum_{q\ge1} b_q<\infty$.

For a nonnegative integer $K$, write $M_{>K}(n)$ for the part of $M(n)$ from denominators strictly above $K$, with the original arc weights. Every window with $j\ge1$ satisfies

$$
\frac{1}{W_j}\sum_{n\in T_j}|M_{>K}(n)|\le 4d\sum_{q>K} b_q.
$$

The same cutoff $K$ therefore works for every window at that modulus. For each fixed $q$, the retained arc mass tends to one. The summable bound allows this limit to pass through the sum over all denominators. At each fixed positive target the complete sum is absolutely convergent. Expanding the finite Euler product over primes up to a cutoff and passing to the limit identifies it with $2C_2 S(n)$, including the local factor at $2$. ([Prefix bound and uniform tail](ConductorTail.lean), [Euler product identification](RamanujanMainTerm.lean), [arc mass normalization](ArcMassNormalization.lean))

### Unconditional density for the frozen signed floor

Fix a positive integer $d$. For an index $j\ge 1$, let $T_j$ consist of the $j$ integers $n=di$ with $j\le i<2j$, and put $W_j=\sum_{n\in T_j}n$. Let $I(n)$ denote the real part of the exact catalogue integral with both prime factors above the cube-root cutoff. The reference checker proves

$$
\lim_{j\to\infty}\frac{1}{W_j}\sum_{n\in T_j}|I(n)|=0,\qquad
\lim_{j\to\infty}\frac{\#\{n\in T_j:I(n)<-\varepsilon n\}}{j}=0
\quad(\varepsilon>0).
$$

At $d=2$ this gives the proposed catalogue entry with its original arcs, high-prime weights and target phase. No classical Goldbach mean-square estimate is assumed. The pointwise floor still requires controlling the remaining sparse exceptions. The density theorem submitted in [PR #1667](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1667) counts targets with no representation in a prescribed prime interval. Here the measured quantity is the signed real Fourier coefficient at its original target-dependent cutoff. ([Count and frozen-integral theorems](UnconditionalDensity.lean), [exact catalogue type and checker](check.py))

**One prime spectrum for the whole window.** Put $X=2dj$ and $Q=\lfloor\log_2(X+2)\rfloor^{20}$. Retain the full log-prime spectrum through $X$. For any $n\le X$, its squared spectrum integrated against the $n$th character on the full circle gives exactly the ordered weighted count $R(n)$. Outside the arcs of radii $Q/(qX)$ the uniform Vaughan estimate at exponent two bounds the spectrum by $X/(\log X)^2$. The fourth-moment inequality then bounds the sum of the squared norms of any initial segment of minor-arc coefficients by $2X^3/(\log X)^2$ for all sufficiently large $X$. Cauchy–Schwarz gives vanishing weighted mean absolute error. The arbitrary-frequency rational-arc approximation uses one error threshold for all $n\le X$. ([Common-spectrum minor estimate](WideMinorMean.lean), [full coefficient and major-arc accuracy](CommonArcProjection.lean))

**Recovering the target-dependent main term.** For the discrete kernel $D_X(t)=\sum_{k=0}^X e^{2\pi i k t}$, the $n$th coefficient of its square on a full period is $n+1$ when $n\le X$. Integrating only over $[-b,b]$, with $0<b\le 1/2$, changes this coefficient by at most $2/b$, uniformly in $n$. This follows by integrating the inverse-square bound for the geometric sum over the two omitted intervals. The integral also has norm at most $X+1$. For $X/2\le n\le X$ these estimates bound the error in each positive-denominator factor relative to $n$ by $\min\{4,(4q+2)/Q\}$, including omitted denominators. This tends to zero at every fixed $q$ and is dominated by the summable arithmetic weights established above. Both arc models therefore approximate the same classical main term on the window. Applying the earlier pointwise transfer from the count to the frozen real part gives the stated limits. ([Uniform kernel bounds](CommonKernelTail.lean), [summation over denominators](CommonModelMean.lean))

The checker extracts five sections from the pinned [PR #1667 proof](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/813ca8c4a3e6ab6ef53180fc5a2c56275a19db88/lean/PEqualNP/Outside/L_goldbach_bulk_density_one.lean). It verifies the full source digest before extraction. The selected sections contain the Vaughan estimate, the fourth-moment estimate, the Dirichlet kernel coefficients, the arbitrary-cutoff square-model error and the rational-arc geometry. They retain the upstream proof's credits, including the OpenAI Vaughan development, DFQDZZ's #316 major-arc estimates, and the finite Fourier work used in #1667. ([Extraction ranges and pinned inputs](check.py))

### 本地复核

在仓库根目录执行以下命令。检查程序核对固定版本的弧不交引理、截断尺度引理以及 PR #316、#1667 的源码摘要，随后编译各证明模块。它还从目录逐字读取前缀等价式、主弧下界、计数等价式和有符号下界的例外密度命题，检查证明是否具有相应的类型，最后用 Lean 内核重检所有模块。（[复核程序](check.py)）

```sh
(cd lean && lake exe cache get)
python3 research/reference-proofs/prime-band/check.py
```
