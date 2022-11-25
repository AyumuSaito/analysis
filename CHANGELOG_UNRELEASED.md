# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
  + structures `sigma_finite_additive_measure` and `sigma_finite_measure`

- in file `topology.v`,
  + new definition `perfect_set`.
  + new lemmas `perfectTP`, `perfect_prod`, and `perfect_diagonal`.
- in `constructive_ereal.v`:
  + lemmas `EFin_sum_fine`, `sumeN`
  + lemmas `adde_defDr`, `adde_def_sum`, `fin_num_sumeN`
  + lemma `fin_num_adde_defr`, `adde_defN`

- in `constructive_ereal.v`:
  + lemma `oppe_inj`

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in `classical_sets.v`:
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `finite_measure_sigma_finite`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`
  + product measures now take `{measure _ -> _}` arguments and their
    theory quantifies over a `{sigma_finite_measure _ -> _}`.

- in `classical_sets.v`:
  + lemma `trivIset_mkcond`
- in `numfun.v`:
  + lemmas `xsection_indic`, `ysection_indic`
- in `classical_sets.v`:
  + lemmas `xsectionI`, `ysectionI`
- in `lebesgue_integral.v`:
  + notations `\x`, `\x^` for `product_measure1` and `product_measure2`
  + notations `\bigcup_(i < n) F` and `\bigcap_(i < n) F`
- in `contructive_ereal.v`:
  + multi-rules `lteey`, `lteNye`
- in `lebesgue_integral.v`:
  + lemma `integral_cstNy`
  + lemma `ae_eq0`
  + lemma `integral_cst`

- in `fsbig.v`:
  + lemma `fsbig_setU_set1`
- in `tooplogy.v`:
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`


- in file `classical_sets.v`,
  + new lemmas `eq_image_id`, `subKimage`, `subimageK`, and `eq_imageK`.
- in file `functions.v`,
  + new lemmas `inv_oppr`, `preimageEoinv`, `preimageEinv`, and
    `inv_funK`.
- in file `mathcomp_extra.v`,
  + new definition `inv_fun`.
  + new lemmas `ler_ltP`, and `real_ltr_distlC`.
- in file `constructive_ereal.v`,
  + new lemmas `real_ltry`, `real_ltNyr`, `real_leey`, `real_leNye`,
    `fin_real`, `addNye`, `addeNy`, `gt0_muley`, `lt0_muley`, `gt0_muleNy`, and
    `lt0_muleNy`.
  + new lemmas `daddNye`, and `daddeNy`.
- in file `ereal.v`,
  + new lemmas `ereal_nbhs_pinfty_gt`, `ereal_nbhs_ninfty_lt`,
    `ereal_nbhs_pinfty_real`, and `ereal_nbhs_ninfty_real`.
- in file `normedtype.v`,
  + new lemmas `nbhsNimage`, `nbhs_pinfty_real`, `nbhs_ninfty_real`,
    `pinfty_ex_ge`, `cvgryPger`, `cvgryPgtr`, `cvgrNyPler`, `cvgrNyPltr`,
    `cvgry_ger`, `cvgry_gtr`, `cvgrNy_ler`, `cvgrNy_ltr`, `cvgNry`, `cvgNrNy`,
    `cvgry_ge`, `cvgry_gt`, `cvgrNy_le`, `cvgrNy_lt`, `cvgeyPger`, `cvgeyPgtr`,
    `cvgeyPgty`, `cvgeyPgey`, `cvgeNyPler`, `cvgeNyPltr`, `cvgeNyPltNy`,
    `cvgeNyPleNy`, `cvgey_ger`, `cvgey_gtr`, `cvgeNy_ler`, `cvgeNy_ltr`,
    `cvgNey`, `cvgNeNy`, `cvgerNyP`, `cvgeyPge`, `cvgeyPgt`, `cvgeNyPle`,
    `cvgeNyPlt`, `cvgey_ge`, `cvgey_gt`, `cvgeNy_le`, `cvgeNy_lt`, `cvgenyP`,
    `normfZV`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`,
    `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`,
    `nbhs_norm0P`, `cvgr0Pnorm_lt`, `cvgr0_norm_lt`, `cvgr0_norm_le`, `nbhsDl`,
    `nbhsDr`, `nbhs0P`, `nbhs_right0P`, `nbhs_left0P`, `nbhs_right_gt`,
    `nbhs_left_lt`, `nbhs_right_neq`, `nbhs_left_neq`, `nbhs_right_ge`,
    `nbhs_left_le`, `nbhs_right_lt`, `nbhs_right_le`, `nbhs_left_gt`,
    `nbhs_left_ge`, `nbhsr0P`, `cvgrPdist_le`, `cvgrPdist_ltp`,
    `cvgrPdist_lep`, `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`,
    `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`, `cvgr0Pnorm_lep`, `cvgr_norm_lt`,
    `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`, `cvgr_neq0`,
    `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`,
    `cvgr_gt`, `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`,
    `cvgr_norm_geNy`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`, `cvgr2dist_lt`,
    `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvgr_to_ge`, `cvgr_to_le`,
    `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`,
    `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `neq0_fine_cvgP`,
    `cvgeNP`, `is_cvgeNE`, `cvge_to_ge`, `cvge_to_le`, `is_cvgeM`, `limeM`,
    `cvge_ge`, `cvge_le`, `lim_nnesum`, `ltr0_cvgV0`, `cvgrVNy`, `ler_cvg_to`,
    `gee_cvgy`, `lee_cvgNy`, `squeeze_fin`, and `lee_cvg_to`.
- in file `sequences.v`,
  + new lemma `nneseries_pinfty`.
- in file `topology.v`,
  + new lemmas `eq_cvg`, `eq_is_cvg`, `eq_near`, `cvg_toP`, `cvgNpoint`,
    `filter_imply`, `nbhs_filter`, `near_fun`, `cvgnyPgt`, `cvgnyPgty`,
    `cvgnyPgey`, `fcvg_ballP`, `fcvg_ball`, and `fcvg_ball2P`.
- in `topology.v`, added `near do` and `near=> x do` tactic notations
  to perform some tactics under a `\forall x \near F, ...` quantification.
- in `normedtype.v`, added notations `^'+`, `^'-`, `+oo_R`, `-oo_R`
- in `measure.v`:
  + definition `discrete_measurable_bool` with an instance of measurable type
  + lemmas `measurable_fun_if`, `measurable_fun_ifT`
- in `constructive_ereal.v`:
  + lemmas `expeS`, `fin_numX`

- in `functions.v`:
  + lemma `countable_bijP`
  + lemma `patchE`
- in file `mathcomp_extra.v`,
  + new definitions `proj`, and `dfwith`.
  + new lemmas `dfwithin`, `dfwithout`, and `dfwithP`.
- in `measure.v`:
  + lemma `measurable_fun_bool`
- in `constructive_ereal.v`:
  + lemma `lt0e`
- in `lebesgue_integral.v`:
  + lemma `le_integral_comp_abse`

- in file `topology.v`,
  + new definitions `countable_uniformity`, `countable_uniformityT`, 
    `sup_pseudoMetric_mixin`, `sup_pseudoMetricType`, and 
    `product_pseudoMetricType`.
  + new lemmas `countable_uniformityP`, `countable_sup_ent`, and 
    `countable_uniformity_metric`.

- in `constructive_ereal.v`:
  + lemmas `adde_def_doppeD`, `adde_def_doppeB`
  + lemma `fin_num_sume_distrr`
- in `classical_sets.v`:
  + lemma `coverE`

- in file `topology.v`,
  + new definitions `quotient_topology`, and `quotient_open`.
  + new lemmas `pi_continuous`, `quotient_continuous`, and
    `repr_comp_continuous`.

- in file `boolp.v`,
  + new lemma `forallp_asboolPn2`.
- in file `classical_sets.v`,
  + new lemma `preimage_range`.
- in file `topology.v`,
  + new definitions `hausdorff_accessible`, `separate_points_from_closed`, and 
    `join_product`.
  + new lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`, 
    `join_product_continuous`, `join_product_open`, `join_product_inj`, and 
    `join_product_weak`. 
- in `measure.v`:
  + structure `FiniteMeasure`, notation `{finite_measure set _ -> \bar _}`

- in `measure.v`:
  + definition `sfinite_measure_def`
  + mixin `Measure_isSFinite_subdef`, structure `SFiniteMeasure`,
    notation `{sfinite_measure set _ -> \bar _}`
  + mixin `SigmaFinite_isFinite` with field `fin_num_measure`, structure `FiniteMeasure`,
    notation `{finite_measure set _ -> \bar _}`
  + lemmas `sfinite_measure_sigma_finite`, `sfinite_mzero`, `sigma_finite_mzero`, `finite_mzero`
  + factory `Measure_isFinite`, `Measure_isSFinite`
  + lemma `sfinite_measure`
  + mixin `FiniteMeasure_isSubProbability`, structure `SubProbability`,
    notation `subprobability`
  + factory `Measure_isSubProbability`
  + factory `FiniteMeasure_isSubProbability`
  + factory `Measure_isSigmaFinite`
  + lemmas `fin_num_fun_finite_measure`, `finite_measure_fin_num_fun`
  + definition `fin_num_fun`
  + structure `FinNumFun`
  + definition `finite_measure2`
  + lemmas `finite_measure2_finite_measure`, `finite_measure_finite_measure2`
- in `lebesgue_measure.v`:
  + definition `fimfunE` now uses fsbig
- in `sequence.v`:
  + `nneseries_pinfty` generalized to `eseries_pinfty`
- in `lebesgue_measure.v`:
  + generalize and rename `eitv_c_infty` to `eitv_bnd_infty` and
    `eitv_infty_c` to `eitv_infty_bnd`
  + generalize `ErealGenOInfty.G`, `ErealGenCInfty.G`, `ErealGenInftyO.G`
- in `lebesgue_integral.v`:
  + implicits of `ae_eq_integral`

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`
- move from `lebesgue_integral.v` to `classical_sets.v`
  + lemmas `trivIset_preimage1`, `trivIset_preimage1_in`
- move from `lebesgue_integral.v` to `numfun.v`
  + lemmas `fimfunE`, `fimfunEord`, factory `FiniteDecomp`
  + lemmas `fimfun_mulr_closed`
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`
  + defintion `fimfun_ringMixin`
  + lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    `indic_fimfun_subproof`.
  + definitions `indic_fimfun`, `scale_fimfun`, `fimfun_comRingMixin`
  + canonical `fimfun_comRingType`
  + lemma `max_fimfun_subproof`
  + mixin `IsNonNegFun`, structure `NonNegFun`, notation `{nnfun _ >-> _}`

- in `measure.v`:
  + `finite_measure` is now a lemma that applies to a finite measure
  + order of arguments of `isContent`, `Content`, `measure0`, `isMeasure0`,
    `Measure`, `isSigmaFinite`, `SigmaFiniteContent`, `SigmaFiniteMeasure`

### Renamed

- in `measurable.v`:
  + `measurable_fun_comp` -> `measurable_funT_comp`
- in `numfun.v`:
  + `IsNonNegFun` -> `isNonNegFun`
- in `lebesgue_integral.v`:
  + `IsMeasurableFunP` -> `isMeasurableFun`
- in `measure.v`:
  + `{additive_measure _ -> _}` -> `{content _ -> _}`
  + `isAdditiveMeasure` -> `isContent`
  + `AdditiveMeasure` -> `Content`
  + `additive_measure` -> `content`
  + `additive_measure_snum_subproof` -> `content_snum_subproof`
  + `additive_measure_snum` -> `content_snum`
  + `SigmaFiniteAdditiveMeasure` -> `SigmaFiniteContent`
  + `sigma_finite_additive_measure` -> `sigma_finite_content`
  + `{sigma_finite_additive_measure _ -> _}` -> `{sigma_finite_content _ -> _}`
- in `constructive_ereal.v`:
  + `fin_num_adde_def` -> `fin_num_adde_defl`
  + `oppeD` -> `fin_num_oppeD`
  + `oppeB` -> `fin_num_oppeB`
  + `doppeD` -> `fin_num_doppeD`
  + `doppeB` -> `fin_num_doppeB`
- in `topology.v`:
  + `finSubCover` -> `finite_subset_cover`
 + `pasting` -> `withinU_continuous`
- file `theories/boolp.v` -> `classical/boolp.v`
- file `theories/classical_sets.v` -> `classical/classical_sets.v`
- file `theories/functions.v` -> `classical/functions.v`
- file `theories/cardinality.v` -> `classical/cardinality.v`
- file `theories/fsbigop.v` -> `classical/fsbigop.v`
- in `sequences.v`:
  + `nneseries0` -> `eseries0`
  + `nneseries_pred0` -> `eseries_pred0`
  + `eq_nneseries` -> `eq_eseries`
  + `nneseries_mkcond` -> `eseries_mkcond`
- in `mathcomp_extra.v`:
  + `homo_le_bigmax` -> `le_bigmax2`
- in `sequences.v`:
  + `seqDUE` -> `seqDU_seqD`
- file `theories/mathcomp_extra.v` moved to `classical/mathcomp_extra.v`
- `theories/set_interval.v` -> `theories/real_interval.v`
- in `lebesgue_integral.v`:
  + `integral_cst_pinfty` -> `integral_csty`
  + `sintegral_cst` -> `sintegral_EFin_cst`
  + `integral_cst` -> `integral_cstr`

- in file `constructive_ereal.v`,
  + `esum_ninftyP` -> `esum_eqNyP`
  + `esum_ninfty` -> `esum_eqNy`
  + `esum_pinftyP` -> `esum_eqyP`
  + `esum_pinfty` -> `esum_eqy`
  + `desum_pinftyP` -> `desum_eqyP`
  + `desum_pinfty` -> `desum_eqy`
  + `desum_ninftyP` -> `desum_eqNyP`
  + `desum_ninfty` -> `desum_eqNy`
  + `eq_pinftyP` -> `eqyP`
- in file `lebesgue_measure.v`,
  + `measurable_fun_elim_sup` -> `measurable_fun_lim_esup`
- in file `measure.v`,
  + `caratheodory_lim_lee` -> `caratheodory_lime_le`
- in file `normedtype.v`,
  + `normmZ` -> `normrZ`
  + `norm_cvgi_map_lim` -> `norm_cvgi_lim`
  + `nbhs_image_ERFin` -> `nbhs_image_EFin`
- moved from `sequences.v` to `normedtype.v`:
  + `squeeze` -> `squeeze_cvgr`
- moved from `lebesgue_measure.v` to `real_interval.v`:
  + `itv_cpinfty_pinfty` -> `itv_cyy`
  + `itv_opinfty_pinfty` -> `itv_oyy`
  + `itv_cninfty_pinfty` -> `itv_cNyy`
  + `itv_oninfty_pinfty` -> `itv_oNyy`
- in file `sequences.v`,
  + `elim_sup` -> `lim_esup`
  + `elim_inf` -> `lim_einf`
  + `elim_inf_shift` -> `lim_einf_shift`
  + `elim_sup_le_cvg` -> `lim_esup_le_cvg`
  + `elim_infN` -> `lim_einfN`
  + `elim_supN` -> `lim_esupN`
  + `elim_inf_sup` -> `lim_einf_sup`
  + `cvg_ninfty_elim_inf_sup` -> `cvgNy_lim_einf_sup`
  + `cvg_ninfty_einfs` -> `cvgNy_einfs`
  + `cvg_ninfty_esups` -> `cvgNy_esups`
  + `cvg_pinfty_einfs` -> `cvgy_einfs`
  + `cvg_pinfty_esups` -> `cvgy_esups`
  + `cvg_elim_inf_sup` -> `cvg_lim_einf_sup`
  + `is_cvg_elim_infE` -> `is_cvg_lim_einfE`
  + `is_cvg_elim_supE` -> `is_cvg_lim_esupE`
- in file `topology.v`,
  + `cvg_map_lim` -> `cvg_lim`
  + `cvgi_map_lim` -> `cvgi_lim`
  + `app_cvg_locally` -> `cvg_ball`
- in file `topology.v`,
  + `prod_topo_apply_continuous` -> `proj_continuous`
- in `constructive_ereal.v`:
  + `ltey` -> `ltry`
  + `ltNye` -> `ltNyr`

### Generalized

- in `esum.v`:
  + lemma `esum_esum`
- in `measure.v`
  + lemma `measurable_fun_comp`
- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`
- in `measure.v`:
  + lemma `measure_bigcup` generalized,
- in `classical_sets.v`:
  + `xsection_preimage_snd`, `ysection_preimage_fst`
  + `integral_sum` -> `integral_nneseries`
- in `constructive_ereal.v`:
  + `ltey`, `ltNye`

### Deprecated

- in `constructive_ereal.v`:
  + `oppeD`, `oppeB`
- in `measure.v`:
  + `sigma_finite` generalized from `numFieldType` to `numDomainType`
  + `finite_measure_sigma_finite` generalized from `measurableType` to `algebraOfSetsType`

### Deprecated

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

### Infrastructure

### Misc
