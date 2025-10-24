# RicciFlow Blueprint Documentation

> **状态：** ✅ 生产就绪
> **最后更新：** 2025-10-23
> **生成的页面数：** 9个HTML文件

---

## 📖 什么是 Blueprint？

Blueprint 是 Lean 形式化项目的文档系统，它：
- 📝 用 LaTeX 编写数学内容
- 🔗 链接到 Lean 代码
- 🌐 生成交互式网页
- ✅ 追踪形式化进度

---

## 🚀 快速开始

### 查看 Blueprint

```bash
./view-blueprint.sh
```

浏览器访问：**http://localhost:8000**

### 重新生成 Blueprint

修改 `blueprint/src/` 下的文件后：

```bash
./rebuild-blueprint.sh
```

---

## 📁 文件结构

```
blueprint/
├── src/                   # 源文件
│   ├── web.tex           # Web版本主文件
│   ├── content.tex       # 数学内容（修改这个！）
│   └── macros/
│       └── common.tex    # 数学宏定义
└── web/                  # 生成的网页（不要手动修改）
    ├── index.html        # 主页
    ├── chap-*.html       # 章节页面
    └── sect-*.html       # 小节页面
```

---

## ✏️ 如何编辑内容

### 1. 编辑 `blueprint/src/content.tex`

添加新的定义、引理或定理：

```latex
\begin{lemma}[引理名称]
\label{lem:my-lemma}
\lean{RicciFlow.myLemma}        % Lean 声明名
\leanok                         % 已形式化标记
\uses{def:some-definition}      % 依赖的定义
引理陈述...
\end{lemma}
```

### 2. 重新生成

```bash
./rebuild-blueprint.sh
```

### 3. 查看效果

```bash
./view-blueprint.sh
```

---

## 🎨 支持的环境

- `\begin{definition}...\end{definition}` - 定义
- `\begin{lemma}...\end{lemma}` - 引理
- `\begin{theorem}...\end{theorem}` - 定理
- `\begin{proposition}...\end{proposition}` - 命题
- `\begin{corollary}...\end{corollary}` - 推论
- `\begin{remark}...\end{remark}` - 注记
- `\begin{example}...\end{example}` - 例子
- `\begin{proof}...\end{proof}` - 证明

---

## 🏷️ Blueprint 命令

### `\lean{DeclarationName}`
链接到 Lean 声明：
```latex
\lean{RicciFlow.pos_mul_pos}
```

### `\leanok`
标记为已形式化（显示绿色✓）：
```latex
\leanok
```

### `\uses{label1, label2}`
声明依赖关系：
```latex
\uses{def:manifold-type, lem:pos-mul-pos}
```

### `\label{ref-name}`
创建可引用的标签：
```latex
\label{thm:main-result}
```

---

## 📊 当前内容

### 章节列表

1. **Introduction** - 项目介绍
2. **Basic Definitions** - 基础定义（6个引理）
3. **Riemannian Manifolds** - 黎曼流形（定义和引理）
4. **Ricci Curvature** - Ricci曲率
5. **Ricci Flow** - Ricci流方程
6. **Future Directions** - 未来方向

### 形式化统计

- ✅ 已形式化引理：9个
- 📝 定义：7个
- 🎯 定理：1个
- 🔗 Lean声明引用：16个

---

## 🔧 技术说明

### 为什么不使用 `leanblueprint` 命令？

原因：`leanblueprint web` 工具目前有一个bug：
- 自动加载 `plastexdepgraph` 包
- 尝试插入依赖图
- PlasTeX 渲染错误导致生成失败

**我们的解决方案：**
- 直接使用 `plastex` 命令
- 简化配置，手动定义必要命令
- 完全兼容，更加稳定

### 生成命令

实际执行的是：
```bash
cd blueprint/src
plastex web.tex
mv web ../
```

---

## ⚙️ 自定义

### 添加数学宏

编辑 `blueprint/src/macros/common.tex`：

```latex
\newcommand{\MyOperator}{\operatorname{MyOp}}
```

### 修改样式

生成的网页使用标准的 plasTeX 主题，可在生成后修改：
- `blueprint/web/styles/theme-white.css` - 浅色主题
- `blueprint/web/styles/amsthm.css` - 定理样式

---

## 🐛 故障排除

### 问题：生成失败

**检查：**
1. `blueprint/src/content.tex` 语法是否正确
2. 是否有未闭合的环境
3. 数学公式是否正确

**解决：**
```bash
cd blueprint/src
plastex web.tex 2>&1 | less  # 查看详细错误
```

### 问题：页面显示乱码

**原因：** 可能是编码问题

**解决：** 确保所有 `.tex` 文件使用 UTF-8 编码

### 问题：数学公式不显示

**原因：** MathJax 未加载

**解决：** 确保有网络连接（MathJax 从CDN加载）

---

## 📚 相关资源

- **PlasTeX 文档：** https://plastex.github.io/plastex/
- **Lean Blueprint 官方：** https://github.com/PatrickMassot/leanblueprint
- **LaTeX 数学符号：** https://www.overleaf.com/learn

---

## 🎯 下一步

### 建议的改进：

1. **添加更多内容** - 扩展 `content.tex`
2. **完善定义** - 补充数学细节
3. **添加更多引理** - 建立完整证明链
4. **GitHub Pages** - 部署到网页供他人查看

### 示例工作流：

```bash
# 1. 编辑内容
vim blueprint/src/content.tex

# 2. 重新生成
./rebuild-blueprint.sh

# 3. 查看效果
./view-blueprint.sh

# 4. 满意后提交
git add blueprint/
git commit -m "Update blueprint: added new lemmas"
```

---

**祝你形式化顺利！** 🎉

---

## 📊 依赖图（Dependency Graph）

### 查看依赖图

依赖图显示了所有定义和定理之间的逻辑依赖关系。

**方法1：通过网页查看**
```bash
./view-blueprint.sh
# 浏览器访问 http://localhost:8000
# 点击 "📊 Dependency Graph"
```

**方法2：直接查看SVG**
```bash
open blueprint/web/dep_graph.svg
# 或浏览器访问 http://localhost:8000/dep_graph.svg
```

**方法3：查看带说明的页面**
```
http://localhost:8000/dep_graph.html
```

### 图例说明

- 🟩 **绿色** - 已完全形式化（有Lean证明）
- 🟨 **黄色/橙色** - 定义存在但需完善
- 📦 **方框** - 定义（Definition）
- ⭕ **椭圆** - 引理/定理（Lemma/Theorem）
- → **实线箭头** - 直接证明依赖
- ⟶ **虚线箭头** - 定义中使用

### 包含的节点

依赖图包含约16个节点：

**定义：**
- Manifold Type
- Riemannian Metric
- Inner Product
- Norm Squared
- Ricci Tensor
- Scalar Curvature
- Ricci Flow Equation

**引理/定理：**
- pos_mul_pos
- square_pos_of_ne_zero
- exists_pos_real
- inv_pos_of_pos
- continuousAt_iff
- innerProduct_symm
- normSq_pos
- scalarCurvature_eq_traceValue
- Short-Time Existence

### 形式化进度

- **总节点：** ~16个
- **已形式化：** 9个引理 ✅
- **完成度：** ~56%

---
