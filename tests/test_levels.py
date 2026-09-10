"""
Sanity checks on the SG graph construction and on the operators built
on top of it, across refinement levels m=1..6.
"""
import numpy as np
import pytest

from graph.sg_graph import sg_tree_graph_with_faces, expected_counts
from operators.operators import build_plain_sg, build_su2_bundle


@pytest.mark.parametrize("level", [1, 2, 3, 4, 5, 6])
def test_vertex_edge_face_counts_match_closed_form(level):
    V, E, faces = sg_tree_graph_with_faces(level)
    n_v, n_e, n_f = expected_counts(level)
    assert len(V) == n_v
    assert len(E) == n_e
    assert len(faces) == n_f


@pytest.mark.parametrize("level", [1, 2, 3, 4, 5])
def test_plain_sg_laplacian_is_connected_and_symmetric(level):
    H, n = build_plain_sg(level)
    assert H.shape == (n, n)
    assert np.allclose(H, H.T)
    w = np.linalg.eigvalsh(H)
    w.sort()
    # exactly one zero mode (connected graph) and the rest strictly positive
    assert abs(w[0]) < 1e-9
    assert w[1] > 1e-6


@pytest.mark.parametrize("level", [1, 2, 3])
def test_su2_bundle_reduces_to_two_plain_sg_copies_at_theta_zero(level):
    """theta=0 must give two exactly decoupled copies of the plain SG
    spectrum -- a required consistency check of the whole construction."""
    H_su2, n = build_su2_bundle(level, theta=0.0, commuting=False)
    H_plain, _ = build_plain_sg(level)

    w_su2 = np.linalg.eigvalsh(H_su2)
    w_su2.sort()
    w_plain = np.linalg.eigvalsh(H_plain)
    w_plain.sort()
    expected = np.sort(np.concatenate([w_plain, w_plain]))

    assert np.max(np.abs(w_su2 - expected)) < 1e-10


@pytest.mark.parametrize("level", [1, 2, 3])
def test_su2_bundle_is_hermitian(level):
    H, n = build_su2_bundle(level, theta=1.234, commuting=False)
    assert np.allclose(H, H.conj().T, atol=1e-12)
