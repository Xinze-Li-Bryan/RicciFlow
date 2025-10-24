# Claude Code 专用 Prompts

这里是 7 个精心准备的 prompts，你可以直接复制粘贴给 Claude Code（VSCode 扩展）或 Claude 网页版使用。

---

## 📋 Prompt 索引

1. [实现 RiemannianMetric 结构体](#prompt-1-实现-riemannianmetric-结构体) - ⭐⭐ 中等
2. [实现 scalarCurvature 函数](#prompt-2-实现-scalarcurvature-函数) - ⭐⭐⭐ 中等-困难
3. [添加基础引理](#prompt-3-添加基础引理) - ⭐ 简单
4. [改进 Blueprint 文档](#prompt-4-改进-blueprint-文档) - ⭐⭐ 中等
5. [添加完整例子](#prompt-5-添加完整例子) - ⭐⭐⭐ 中等-困难
6. [调试和清理](#prompt-6-调试和清理) - ⭐⭐ 中等
7. [连接 Mathlib 现有理论](#prompt-7-连接-mathlib-现有理论) - ⭐⭐⭐⭐ 困难

---

## Prompt 1: 实现 RiemannianMetric 结构体

**难度**: ⭐⭐ 中等
**优先级**: 🔥 高
**估计时间**: 1-2 小时

```
我的 Lean 4 项目位于：/Users/lixinze/RicciFlow

文件 RicciFlow/RiemannianManifold.lean 中有一个空的结构体：

structure RiemannianMetric (M : Type*) where
  -- 度量张量的定义

请帮我：
1. 查看 Mathlib4 中关于流形和度量的现有定义
2. 使用 Mathlib 的类型，实现一个简化但数学上正确的 RiemannianMetric
3. 添加基本的性质：对称性、正定性
4. 添加 1-2 个简单的辅助函数（如计算两个向量的内积）

要求：
- 代码要能通过 `lake build`
- 避免过于复杂的依赖
- 每个字段和函数都有清晰的文档注释

完成后，请告诉我：
1. 修改了哪些文件
2. 需要运行什么命令验证
3. 是否需要更新 blueprint
```

---

## Prompt 2: 实现 scalarCurvature 函数

**难度**: ⭐⭐⭐ 中等-困难
**优先级**: 🔥 高
**估计时间**: 2-3 小时

```
我的项目：/Users/lixinze/RicciFlow

文件 RicciFlow/RicciCurvature.lean 中有：

def scalarCurvature {M : Type*} (Ric : RicciTensor M) : ℝ :=
  sorry

这个函数目前用 sorry 占位。请帮我：
1. 查看 Mathlib 中关于张量缩并（tensor contraction）的函数
2. 实现标量曲率的数学定义：R = g^{ij} Ric_{ij}（Ricci 张量的迹）
3. 确保类型检查通过
4. 如果需要额外的类型类约束，请添加并解释
5. 添加一个简单的测试或例子

目标：移除这个 sorry，让 blueprint 显示绿色 ✓

完成后请告诉我：
- 是否成功移除了 sorry
- 需要运行什么验证命令
- 是否需要更新其他文件
```

---

## Prompt 3: 添加基础引理

**难度**: ⭐ 简单
**优先级**: 🎯 中等
**估计时间**: 30 分钟 - 1 小时

```
项目路径：/Users/lixinze/RicciFlow

请帮我在 RicciFlow/Basic.lean 中添加 3-5 个有用的基础引理，例如：
- 关于流形上连续函数的性质
- 关于实数运算的辅助引理
- 关于拓扑空间的简单事实
- 任何对后续模块有帮助的基础结果

要求：
1. 每个引理都有清晰的文档注释（解释它的用途）
2. 尽可能提供完整的证明（避免使用 sorry）
3. 引理应该对 RiemannianManifold、RicciCurvature 或 Flow 模块有帮助
4. 使用 Mathlib 中已有的定理来证明

工作流程：
1. 先列出 3-5 个引理的建议（带简短说明）
2. 等我选择后再实现
3. 或者直接实现你认为最有用的 3 个

完成后请说明：
- 添加了哪些引理
- 它们如何帮助后续开发
```

---

## Prompt 4: 改进 Blueprint 文档

**难度**: ⭐⭐ 中等
**优先级**: 🎯 中等
**估计时间**: 1-2 小时

```
项目路径：/Users/lixinze/RicciFlow
Blueprint 源文件：/Users/lixinze/blueprint/src/web.tex

请帮我改进 blueprint 文档的数学和历史内容：

1. **Chapter 1 (Introduction)**:
   - 扩展 Ricci Flow 的历史背景
   - 解释为什么它在证明庞加莱猜想中重要
   - 添加关键人物：Hamilton, Perelman

2. **每个定义前**:
   - 添加更详细的数学动机
   - 解释它在整体理论中的作用

3. **定理 (short_time_existence)**:
   - 添加详细的证明思路（即使 Lean 代码是 sorry）
   - 解释证明的主要步骤
   - 说明需要的 PDE 理论

4. **参考文献**:
   - 添加关键论文引用
   - Hamilton 1982, Perelman 2002, 等

要求：
- 保持 LaTeX 格式正确
- 数学表述严谨
- 适合数学家阅读

完成后：
1. 告诉我修改了什么
2. 我会运行 `./update-blueprint.sh` 查看效果
```

---

## Prompt 5: 添加完整例子

**难度**: ⭐⭐⭐ 中等-困难
**优先级**: 🌟 中等-低
**估计时间**: 3-4 小时

```
项目：/Users/lixinze/RicciFlow

请创建一个新文件 RicciFlow/Examples.lean，展示理论的实际应用。

内容：
1. **定义一个简单流形**（例如 2-sphere S² 或 R^n）
2. **在上面定义 RiemannianMetric**（标准度量）
3. **如果可能，计算 Ricci 曲率**
4. **展示 Ricci Flow 的行为**（即使是简化版）

要求：
- 尽可能完整，少用 sorry
- 每一步都有详细注释
- 从简单的例子开始（如 R^n 上的欧氏度量）
- 如果 S² 太复杂，可以先做 R^n

额外任务：
1. 更新 RicciFlow.lean 导入这个新文件
2. 在 blueprint/src/web.tex 中添加 Examples 章节
3. 更新 blueprint

目标：让读者看到理论如何应用到具体几何对象上。

完成后请说明：
- 实现了哪个例子
- 哪些部分是完整的，哪些用了 sorry
- 如何在 blueprint 中展示
```

---

## Prompt 6: 调试和清理

**难度**: ⭐⭐ 中等
**优先级**: 🎯 中等
**估计时间**: 1-2 小时

```
项目路径：/Users/lixinze/RicciFlow

请帮我全面审查和清理项目：

1. **构建检查**:
   - 运行 `lake build` 并分析所有输出
   - 列出所有警告（除了预期的 sorry 警告）
   - 检查是否有未使用的导入

2. **Sorry 清单**:
   - 找出所有使用 `sorry` 的地方
   - 为每个评估难度：简单/中等/困难/极难
   - 建议优先解决哪些

3. **代码风格**:
   - 检查是否符合 Lean/Mathlib 惯例
   - 命名是否一致
   - 文档注释是否完整

4. **依赖分析**:
   - 检查是否有不必要的依赖
   - 建议可以简化的地方

输出格式：
- 问题清单（按优先级排序）
- 建议的修复方案
- 预估每项任务的时间

目标：让项目更整洁、更专业。
```

---

## Prompt 7: 连接 Mathlib 现有理论

**难度**: ⭐⭐⭐⭐ 困难
**优先级**: 🌟 中等
**估计时间**: 3-5 小时

```
项目：/Users/lixinze/RicciFlow

Mathlib4 已经有大量的微分几何内容。请帮我系统性地调研和整合：

任务：
1. **搜索 Mathlib**:
   - 查找关于流形的现有定义
   - 查找关于度量张量的定义
   - 查找关于曲率的定义
   - 查找关于微分算子的定义

2. **生成对照表**:
   | 我需要的概念 | Mathlib 是否有 | 位置 | 是否可直接使用 |
   |------------|--------------|------|---------------|
   | 流形 | 是/否 | Module.Name | 是/否 |
   | ... | ... | ... | ... |

3. **重构建议**:
   - 哪些我自己定义的概念应该用 Mathlib 的替换
   - 如何修改代码以利用 Mathlib
   - 有哪些现成的引理可以使用

4. **实施计划**:
   - 分阶段重构的步骤
   - 哪些可以立即做，哪些需要更多研究

目标：
- 避免重复造轮子
- 站在 Mathlib 的肩膀上
- 让项目更符合社区标准

完成后：
- 给出详细的调研报告
- 建议具体的重构方案
- 预估重构的工作量
```

---

## 💡 使用技巧

### 发送 Prompt 的最佳实践

1. **一次一个任务**：不要同时发送多个 prompt
2. **明确当前状态**：告诉 Claude 项目在哪里，文件结构如何
3. **设置期望**：说清楚你想要什么样的输出
4. **要求确认**：让 Claude 告诉你完成后需要做什么验证

### 在每个 Prompt 后加上

```
完成后，请告诉我：
1. 修改了哪些文件（列出完整路径）
2. 需要运行什么命令来验证更改
3. 是否需要更新 blueprint
4. 下一步建议做什么
```

### 如果遇到问题

```
遇到了问题：[描述问题]

当前状态：
- lake build 的输出：[粘贴输出]
- 错误信息：[粘贴错误]

请帮我：
1. 诊断问题
2. 提供解决方案
3. 解释为什么会出现这个问题
```

---

## 🎯 建议的执行顺序

### Week 1: 基础完善
1. ✅ Prompt 3 (添加基础引理) - 简单，快速胜利
2. ✅ Prompt 1 (实现 RiemannianMetric) - 核心任务
3. ✅ Prompt 6 (调试和清理) - 保持整洁

### Week 2: 深入理论
4. ✅ Prompt 2 (实现 scalarCurvature) - 移除 sorry
5. ✅ Prompt 7 (连接 Mathlib) - 理解生态系统
6. ✅ Prompt 4 (改进 Blueprint) - 提升文档质量

### Week 3+: 扩展应用
7. ✅ Prompt 5 (添加例子) - 让理论具体化
8. ✅ 重复 Prompt 6 (定期清理)

---

## 📊 跟踪进度

在完成每个 Prompt 后：

```bash
cd /Users/lixinze/RicciFlow

# 1. 验证构建
lake build

# 2. 更新 blueprint
./update-blueprint.sh

# 3. 查看进度
./view-blueprint.sh
# 打开 http://localhost:8000
```

在 blueprint 中你会看到：
- 🟢 绿色 ✓ 增加 = 进度！
- 🔴 红色 ✗ 减少 = 成功！

---

## 🎉 里程碑奖励

- **第一个 sorry 消除**: 🎊
- **50% sorry 消除**: 🎉
- **所有基础定义完成**: 🏆
- **第一个完整例子**: 🌟
- **Blueprint 全绿**: 💚

---

## 📝 记录模板

在你的笔记本中记录每次任务：

```markdown
## [日期] - 任务：[Prompt 名称]

**使用的 Prompt**: Prompt X
**开始时间**: [时间]
**完成时间**: [时间]

### 修改的文件
- [ ] 文件1
- [ ] 文件2

### 遇到的问题
1. [问题描述]
   - 解决方案：[...]

### 学到的东西
- [关键点1]
- [关键点2]

### 下一步
- [ ] 任务1
- [ ] 任务2
```

---

**准备好了吗？** 选择一个 Prompt 开始吧！🚀

建议从 **Prompt 3** 开始（简单的基础引理），快速获得成就感！
