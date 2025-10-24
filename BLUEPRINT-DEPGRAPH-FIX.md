# Blueprint 依赖关系图修复报告

## 🔍 问题诊断

### 发现的问题

1. **Blueprint Web 页面缺少依赖图**
   - 症状: 只显示文字，`<div class="centered">  </div>` 是空的
   - 原因: PlasTeX 无法正确渲染 LaTeX 的 `\includegraphics` 命令到 HTML

2. **没有定理级别的依赖图**
   - 只有模块级别的导入图 (`import_graph.dot`)
   - 缺少定理和定义之间的逻辑依赖关系可视化

3. **依赖图生成流程不完整**
   - leanblueprint 需要手动配置才能生成依赖图
   - 没有自动化脚本保持图的更新

---

## ✅ 已实施的修复

### 1. 创建了定理依赖图

**文件**: `blueprint/src/dep_graph.dot`

包含的节点:
- ✅ **绿色**: 完整实现
  - Manifold Type (Basic)
  - pos_mul_pos
  - square_pos_of_ne_zero
  - exists_pos_real
  - inv_pos_of_pos
  - continuousAt_iff

- 🟡 **黄色**: 部分实现/公理
  - Riemannian Metric
  - Ricci Tensor
  - Ricci Flow Equation

- 🔴 **红色**: 使用 sorry
  - Scalar Curvature
  - Short-Time Existence

依赖关系:
```
Manifold Type → Riemannian Metric → Ricci Tensor → Scalar Curvature
                                   ↓
                            Ricci Flow Equation → Short-Time Existence
```

### 2. 生成了 SVG 图形

**文件**: `/Users/lixinze/blueprint/web/dep_graph.svg`
- 大小: 8.9 KB
- 格式: SVG (可缩放矢量图)
- 工具: Graphviz dot

### 3. 修复了 HTML 显示

**修改**: `/Users/lixinze/blueprint/web/index.html`

从:
```html
<div class="centered">  </div>
```

改为:
```html
<div class="centered">
<img src="dep_graph.svg" alt="Dependency Graph" style="max-width: 100%; height: auto;">
</div>
```

### 4. 更新了 LaTeX 源文件

**文件**: `blueprint/src/web.tex`

添加了附录章节 "Dependency Graph"，包含:
- 图形说明
- 颜色编码解释
- 依赖关系说明

### 5. 创建了自动化脚本

**文件**: `scripts/update-dep-graph.sh`

功能:
1. 生成模块导入图
2. 生成 blueprint 依赖图
3. 转换为 SVG
4. 重新生成 blueprint
5. 修复 HTML 中的图形显示

---

## 📊 验证结果

### ✅ 文件清单

```
/Users/lixinze/blueprint/web/
├── dep_graph.svg          ✅ 8.9 KB (新创建)
├── import_graph.svg       ✅ 930 B (模块导入图)
├── index.html             ✅ 已修复 (包含 <img> 标签)
└── symbol-defs.svg        ✅ 12 KB (数学符号)

/Users/lixinze/blueprint/src/
├── dep_graph.dot          ✅ 新创建 (依赖图源文件)
└── web.tex                ✅ 已更新 (添加附录)

/Users/lixinze/RicciFlow/scripts/
└── update-dep-graph.sh    ✅ 新创建 (自动化脚本)
```

### ✅ Graphviz 工作正常

```bash
$ which dot
/usr/local/bin/dot

$ dot -V
dot - graphviz version 14.0.0
```

### ✅ Blueprint 生成成功

```
plasTeX version 3.1
✔ HTML files generated
⚠️ 1 warning (已修复): includegraphics rendering
```

---

## 🚀 使用方法

### 查看依赖图

1. **方式 A: 在浏览器中查看**
   ```bash
   open /Users/lixinze/blueprint/web/index.html
   ```
   滚动到 "Appendix A: Dependency Graph"

2. **方式 B: 启动 Web 服务器**
   ```bash
   cd /Users/lixinze/RicciFlow
   ./view-blueprint.sh
   ```
   访问 http://localhost:8000，导航到 Dependency Graph

3. **方式 C: 直接查看 SVG**
   ```bash
   open /Users/lixinze/blueprint/web/dep_graph.svg
   ```

### 更新依赖图

当你添加新的定理或改变依赖关系时:

```bash
# 方法 1: 使用完整的 blueprint 更新脚本
cd /Users/lixinze/RicciFlow
./update-blueprint.sh

# 方法 2: 只更新依赖图
cd /Users/lixinze/RicciFlow
./scripts/update-dep-graph.sh
```

### 编辑依赖图

1. **编辑源文件**:
   ```bash
   vim /Users/lixinze/RicciFlow/blueprint/src/dep_graph.dot
   ```

2. **添加新节点**:
   ```dot
   new_theorem [label="My New Theorem", fillcolor="#FFB6C1", color="red"];
   new_theorem -> existing_def;
   ```

3. **重新生成**:
   ```bash
   dot -Tsvg blueprint/src/dep_graph.dot -o /Users/lixinze/blueprint/web/dep_graph.svg
   ```

---

## 📈 依赖图说明

### 颜色编码

| 颜色 | 含义 | 示例 |
|------|------|------|
| 🟢 绿色 | 完整实现，无 sorry | pos_mul_pos, Basic 模块 |
| 🟡 黄色 | 部分实现或公理 | RiemannianMetric, ricci_flow_equation |
| 🔴 红色 | 使用 sorry | scalarCurvature, short_time_existence |

### 箭头类型

- **实线箭头**: 直接的逻辑依赖
  - 例: `Ricci Tensor → Scalar Curvature`

- **虚线箭头**: 间接依赖或辅助引理
  - 例: `RiemannianMetric ⇢ pos_mul_pos`

### 图的层次结构

```
Level 1: 基础引理
  ├─ pos_mul_pos
  ├─ square_pos_of_ne_zero
  ├─ exists_pos_real
  ├─ inv_pos_of_pos
  └─ continuousAt_iff

Level 2: 基础定义
  └─ Manifold Type

Level 3: 度量结构
  └─ Riemannian Metric

Level 4: 曲率
  ├─ Ricci Tensor
  └─ Scalar Curvature

Level 5: 流方程
  ├─ Ricci Flow Equation
  └─ Short-Time Existence
```

---

## 🔧 技术细节

### PlasTeX 的限制

**问题**: PlasTeX (用于生成 HTML) 无法正确处理 `\includegraphics`

**解决方案**:
- 在 LaTeX 中保留 `\includegraphics` (用于 PDF 生成)
- 手动在 HTML 中插入 `<img>` 标签
- 使用脚本自动化这个过程

### Graphviz 配置

**节点样式**:
```dot
node [shape=box, style=filled, fontname="Arial"];
```

**颜色方案**:
```dot
fillcolor="#90EE90"  // 淡绿色 (完成)
fillcolor="#FFFFE0"  // 淡黄色 (部分)
fillcolor="#FFB6C1"  // 淡红色 (未完成)
```

**布局方向**:
```dot
rankdir=TB;  // Top to Bottom (从上到下)
```

---

## 💡 下一步改进

### 短期 (可选)

1. **自动化依赖图生成**
   - 从 Lean 代码自动提取依赖关系
   - 使用 `lake exe graph` 的输出

2. **交互式依赖图**
   - 使用 D3.js 或 Cytoscape.js
   - 可点击节点查看详情

3. **颜色自动更新**
   - 根据 Lean 代码中的 sorry 自动标记红色
   - 使用 `leanblueprint checkdecls`

### 长期 (可选)

1. **多视图依赖图**
   - 模块级别
   - 定理级别
   - 按主题分组

2. **进度追踪**
   - 显示完成百分比
   - 随时间变化的动画

3. **与 GitHub 集成**
   - 自动在 CI 中生成
   - 在 PR 中显示依赖变化

---

## 📝 故障排除

### 问题: 依赖图不显示

**检查**:
```bash
# 1. SVG 文件是否存在
ls -lh /Users/lixinze/blueprint/web/dep_graph.svg

# 2. HTML 中是否有 img 标签
grep -A2 "dep_graph" /Users/lixinze/blueprint/web/index.html

# 3. 重新生成
cd /Users/lixinze/RicciFlow
./scripts/update-dep-graph.sh
```

### 问题: 图不更新

**解决**:
```bash
# 清理并重新生成
cd /Users/lixinze
rm -rf blueprint/web/*
leanblueprint web
# 然后运行 update-dep-graph.sh
```

### 问题: Graphviz 错误

**检查**:
```bash
# 验证 dot 文件语法
dot -Tsvg blueprint/src/dep_graph.dot -o /tmp/test.svg

# 如果有错误，检查 .dot 文件的语法
```

---

## ✅ 总结

### 修复完成 ✅

- ✅ 诊断了问题 (PlasTeX 无法渲染图片)
- ✅ 创建了定理依赖图 (dep_graph.dot)
- ✅ 生成了 SVG 图形 (8.9 KB)
- ✅ 修复了 HTML 显示
- ✅ 更新了 LaTeX 源文件
- ✅ 创建了自动化脚本

### 现在可以 ✅

- ✅ 在 blueprint 中看到完整的依赖关系图
- ✅ 清楚地看到哪些部分完成 (绿色)
- ✅ 看到定理之间的逻辑依赖
- ✅ 使用脚本自动更新图

---

**问题已完全解决！** 🎉

现在去查看你的 blueprint:
```bash
open /Users/lixinze/blueprint/web/index.html
```

或者

```bash
cd /Users/lixinze/RicciFlow
./view-blueprint.sh
```

然后滚动到 "Appendix A: Dependency Graph" 查看漂亮的依赖关系图！
