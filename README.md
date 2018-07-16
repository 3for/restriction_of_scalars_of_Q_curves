# restriction_of_scalars_of_Q_curves
This is the Sage (and Magma) code used to extend Nakamura's computation of endomorphism algebras of the restriction of scalars of Gross Q-curves with CM by a field of class group C2 x C2

The main file is nakamura.sage. In order to run it, you need to have the files fields.sage and non_abelian_extensions.sage in the same directory. Running nakamura.sage produces Table 1 (in Latex format) of the article "Endomorphism algebras of geometrically split abelian surfaces over Q".

Even if it is a Sage code, it calls Magma at some points to compute Galois groups. So it is necessary to have Magma installed to run it.
