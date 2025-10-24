# Ricci Flow Blueprint

这是 Ricci Flow 形式化项目的 Blueprint（蓝图）文档系统。

## 文件结构

```
blueprint/
├── src/              # LaTeX 源文件
│   ├── web.tex       # Web 版入口
│   ├── content.tex   # 主要数学内容
│   ├── macros_common.tex  # 数学符号宏定义
│   ├── blueprint.sty # Blueprint 样式包
│   └── plastex.cfg   # PlasTeX 配置
└── web/              # 生成的 HTML 文件
    ├── index.html    # 主页
    ├── chap-*.html   # 各章节
    └── dep_graph.svg # 依赖关系图
```

## 生成 Blueprint

### 方法 1：使用脚本（推荐）

```bash
cd /Users/lixinze/RicciFlow/blueprint/src
./update-blueprint.sh
```

### 方法 2：手动生成

#### 生成 HTML 版本
```bash
cd /Users/lixinze/RicciFlow/blueprint/src
plastex --renderer=HTML5 web.tex
dot -Tsvg dep_graph.dot -o ../web/dep_graph.svg
mv web/* ../web/
rmdir web
```

#### 生成 PDF 版本
```bash
cd /Users/lixinze/RicciFlow/blueprint/src
pdflatex web.tex
# 或使用 latexmk
latexmk -pdf web.tex
```

## 查看 Blueprint

### HTML 版本（推荐）
```bash
# 直接在浏览器打开
open /Users/lixinze/RicciFlow/blueprint/web/index.html

# 或启动本地服务器
cd /Users/lixinze/RicciFlow
leanblueprint serve
# 然后访问 http://localhost:8000
```

### PDF 版本
```bash
open /Users/lixinze/RicciFlow/blueprint/src/web.pdf
```

## VSCode LaTeX 编译

如果 VSCode 的 LaTeX Workshop 显示 "File 'blueprint.sty' not found" 错误：

1. **清理辅助文件**：
   ```bash
   cd /Users/lixinze/RicciFlow/blueprint/src
   latexmk -c
   ```

2. **重新编译**：
   ```bash
   latexmk -pdf web.tex
   ```

3. **或在 VSCode 中**：
   - 打开命令面板（Cmd+Shift+P）
   - 运行 `LaTeX Workshop: Clean up auxiliary files`
   - 运行 `LaTeX Workshop: Build LaTeX project`
   - 如果仍有问题，重启 VSCode

## 编辑 Blueprint

主要内容在 `src/content.tex` 中。使用以下标记链接 Lean 代码：

- `\lean{定理名称}` - 链接到 Lean 定义/定理
- `\leanok` - 标记为已完成形式化（绿色 ✓）
- `\uses{依赖项}` - 声明依赖关系

示例：
```latex
\begin{lemma}[Positive multiplication]
\label{lem:pos-mul-pos}
\lean{RicciFlow.pos_mul_pos}
\leanok
\uses{def:manifold-type}
The product of two positive real numbers is positive.
\end{lemma}
```

## 依赖图

依赖图自动生成，显示定义和定理之间的依赖关系：

- **绿色节点**：已完全形式化
- **黄色节点**：部分实现
- **红色节点**：使用 sorry

## 参考资料

- [Leanblueprint 文档](https://github.com/PatrickMassot/leanblueprint)
- [Sphere Eversion 项目示例](https://leanprover-community.github.io/sphere-eversion/blueprint/)
- [PlasTeX 文档](https://plastex.github.io/plastex/)
