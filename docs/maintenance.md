# 管理用メモ

記事の編集、ローカルでの確認、GitHub Pagesへの公開に関する手順です。コマンドはリポジトリのルートで実行します。

## 初回の公開

1. GitHubの [Settings → Pages](https://github.com/sougyo/PublicArticle/settings/pages) を開き、**Build and deployment → Source** を **GitHub Actions** に変更します。
2. このリポジトリの変更をコミットして `main` へpushします。

   ```bash
   git add .gitignore .github _quarto.yml index.md styles.css articles scripts docs README.md
   git commit -m "Add Quarto mathematics site and GitHub Pages workflow"
   git push origin main
   ```

3. [Actions](https://github.com/sougyo/PublicArticle/actions) の **Publish Quarto site** が成功すると公開されます。既に `main` へpush済みの場合は、Pages設定後に **Run workflow** で実行できます。

以後は `main` へのpushで自動更新されます。Pull RequestではHTMLの生成のみを確認します。公開にはGitHub標準の `GITHUB_TOKEN` を使用し、追加のシークレットや `gh-pages` ブランチは不要です。

公開用ワークフローは [.github/workflows/publish.yml](../.github/workflows/publish.yml) にあります。初回はGitHub側のSource設定が必要です。

## ローカルで確認

[Quarto公式サイト](https://quarto.org/docs/download/)から **Quarto 1.9.38** をインストールし、リポジトリのルートで実行します。CIも同じバージョンを使います。

```bash
quarto preview
```

HTMLだけを生成する場合:

```bash
quarto render
```

生成先は `_site/` です。`_site/` と `.quarto/` はGit管理から除外しています。通常のサイト生成にはPython、R、TeX、Dockerは不要です。

## 記事を編集・追加

- 圏論記事: [articles/category-theory/index.md](../articles/category-theory/index.md)
- トップページ: [index.md](../index.md)
- サイト共通設定: [_quarto.yml](../_quarto.yml)
- 表示スタイル: [styles.css](../styles.css)

`articles/記事名/index.md` を作成し、トップページにリンクを追加します。`articles/**/*.md` は自動的にレンダリング対象になります。ファイル間のリンクは `.md` を指定するとQuartoが公開用の `.html` に変換します。

```markdown
---
title: "新しい記事"
---

# 最初の節

文中の数式は $f : X \to Y$ と書きます。

$$
f(x) = x^2
$$ {#eq-example}

式 [@eq-example] を参照できます。
```

数式は `html-math-method: mathjax` によりブラウザーで描画されます。初回表示にはMathJaxのCDNへの接続が必要です。独自の記号は圏論記事では標準TeXコマンドに展開済みです。表示数式には横スクロールを用意しています。

## 圏論記事の変換について

圏論記事はTeX原稿から変換したものです。17節、81個の定義・定理・例・注意、9個の番号つき数式、計算効果の表をMarkdownへ変換しました。定義などは元の「節番号.通し番号」を維持し、本文の参照をリンクにしました。数式番号はQuartoが振り直します。

TikZの可換図式はMathJaxでは直接表示できないため、15個すべてをSVGに変換して同梱しています。図式内の文字はベクトル化しているため、読者側にTeX用フォントは不要です。図式のTeXソースも `articles/category-theory/diagrams/` に保存しています。

図式を変更する場合のみ、Dockerと `pdftocairo`（Ubuntuでは `poppler-utils`）を用意し、以下を実行します。

```bash
bash scripts/render-diagrams
quarto render
```

必要に応じて `TEX_DOCKER_IMAGE` でTeXイメージを指定できます。SVGはGit管理するため、GitHub ActionsではTeXを実行しません。本文は変換後のMarkdownを直接編集してください。

## 公式ドキュメント

- [Quarto: Markdownと数式](https://quarto.org/docs/authoring/markdown-basics.html)
- [Quarto: GitHub Pagesへの公開](https://quarto.org/docs/publishing/github-pages.html)
- [GitHub: カスタムワークフローによるPages公開](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages)
