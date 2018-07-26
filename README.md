# restriction_of_scalars_of_Q_curves
This is the Sage (and Magma) code used to extend Nakamura's computation of endomorphism algebras of the restriction of scalars of Gross Q-curves with CM by a field of class group C2 x C2

The main file is nakamura.sage. In order to run it, you need to have the files fields.sage and non_abelian_extensions.sage in the same directory. 

You can run the file with the command

sage: %runfile nakamura.sage

and then compute the endomorphism algebras corresponding to Gross Q-curves attached to the field with discriminant D doing 

sage: compute_endomorphism_algebras(D, use_magma_free = False)

Even if it is a Sage code, it calls Magma at some points to compute Galois groups. So it is necessary to have Magma installed to run it. In the above command, you can set use_magma_free = True to perform the computations of the Galois groups using the online Magma calculator (it is necessary to have internet connection).

To reproduce Table 1 of the article "Endomorphism algebras of geometrically split abelian surfaces over Q", uncomment the commented lines at the end, and run the file.
