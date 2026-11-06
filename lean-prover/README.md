# 互動式證明助手(Lean 風格,一階邏輯)

用策略(tactic)一步步縮小目標;策略只負責產生證明項,最後交給約 60 行的**可信核心**重新檢查(de Bruijn 準則)。需要 Node.js 15 以上,無外部套件。

    lean-prover/
    ├── src/lean.js          解析器、核心 check()、策略、報告(Node 與瀏覽器共用)
    ├── bin/cli.js           命令列
    ├── web/template.html    網頁介面;web/index.html 為建置後的單檔網頁版
    ├── scripts/build-web.js 內嵌 lean.js 產生網頁
    ├── examples/*.lean      範例
    └── test/test.js         測試(含「核心拒絕偽造證明」)

## 使用

    npm run demo                              # 執行內建範例
    node bin/cli.js examples/syllogism.lean   # 檢查檔案;加 --trace 逐行顯示目標
    npm test                                  # 測試
    npm run build                             # 修改後重新產生 web/index.html

## 腳本格式

    theorem syllogism (h1 : P -> Q) (h2 : Q -> R) : P -> R := by
      intro hp
      apply h2
      apply h1
      exact hp

`--` 開頭為註解。一個檔案可有多個 theorem。

## 策略

`intro` `exact` `apply` `assumption` `constructor` `left` `right` `cases h with a b` `exists t` `by_contra` `exfalso` `have h := f a` / `have h : A` `show` `sorry`

符號:`~` `&` `|` `->` `<->` `forall x.` `exists x.`(也接受 ¬ ∧ ∨ → ↔ ∀ ∃)。~A 是 A → False 的縮寫,A ↔ B 展開成兩個 →。

## 限制

只有命題與一階邏輯:沒有等號、歸納、型別與自動化(auto)。古典邏輯,`by_contra` 使用雙重否定消去規則。
