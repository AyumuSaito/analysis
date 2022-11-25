* interp_type
  * TODO: P(A) is mesurable ?
    * TODO: pointedType
    * TODO: interp_type (ty_prob _) >-> probability _ _
  * TODO: (A, B) is mesurable -> [the measurable _ of (A * B)%type]
    * TODO: measurable d ~~ measurable (d, d).-prod
* denote_d
  * TODO: denote T_app
  * TODO: denote T_var
* eval term
** TODO: 変数の評価値は実数、ブール値、確率、kernelなどの場合があり、型がひとつに定まっていないので定義するのが難しい

- [ ] generalize bernoulli 
- [x] normalize --d-> _ : probability? measurable-function?
- [x] about var
- [x] need E_realD? / about real (kr r) <- real to kernel

DONE: 変数がリストに入っていることしか確認していない

- [ ] eval_uniq
  - [x] How to use `evalD_mut_ind`
  - [ ] eval_uniqD: `dependent induction e.` don't make I.H.
  - [x] need I.H. about `eval_uniqP` for `eval_uniqD`
  - [ ] `E_var2`の証明のときに`E_var3`,`E_var4`が現れる
  - [ ] `E_norm`でinversionでPとは異なるP0を生み出してしまう
  - [ ] 
- [ ] eval_full

