from functools import reduce, partial
from getopt import getopt, GetoptError
from pathlib import Path
import pickle as pkl
import sys
from tensorflow.keras.models import load_model

def convert_real(x):
    """Pretty-print a float as an Agda floating-point number."""
    return '{0:.15g}'.format(x)

def convert_vector(xs):
    """Pretty-print a Keras vector as a Agda vector."""
    pp = '[]'
    for x in reversed(xs):
        pp = '{x} ∷ {pp}'.format(x=convert_real(x), pp=pp)
    return pp

def convert_matrix(xss):
    """Pretty-print a Keras matrix as a Agda matrix."""
    pp = '[]'
    for xs in reversed(xss.tolist()):
        pp = "({xs})\n∷ {pp}".format(xs=convert_vector(xs), pp=pp)
    return pp

def convert_activation(activation):
    """Pretty-print a Keras activation function as an Amethyst constructor."""
    return 'Activation.' + activation

def indent_by(n, lines):
    """Indent each line after the first by `n`."""
    return lines.replace('\n', '\n'+n*' ')

def convert_layer(index, layer):
    """Pretty-print a Keras layer as an Amethyst definition."""
    params = layer.get_weights()
    weights = params[0]
    rows = weights.shape[0]
    cols = weights.shape[1]
    biases = params[1].reshape((1, -1))
    activation = layer.get_config()['activation']
    return ('layer{index} : Layer Float {rows} {cols}\n'
            'layer{index} = record\n'
            '  {{ weights    = {weights}\n'
            '  ; biases     = {biases}\n'
            '  ; activation = {activation}\n'
            '  }}').format(
                index=index,
                rows=rows,
                cols=cols,
                weights=indent_by(15, convert_matrix(weights)),
                biases=indent_by(15, convert_vector(biases.tolist()[0])),
                activation=convert_activation(activation))

def convert_layer_list(layers, n_in, n_out):
    """"""
    pp = '[]'
    for l in reversed(layers):
        pp = '{l} ∷ {pp}'.format(l=l, pp=pp)
    return ('model : Network Float {n_in} {n_out} {n_layers}\n'
            'model = {layer_list}').format(
                n_in=n_in, n_out=n_out, layer_list=pp, n_layers=len(layers))

def convert_ideal(ideal_label, ideal_in, ideal_out):
    """"""
    n_ideal_in=len(ideal_in)
    n_ideal_out=len(ideal_out)
    return ('ideal{ideal_label}In : Vec Float {n_ideal_in}\n'
            'ideal{ideal_label}In = {ideal_in}\n'
            '\n'
            'ideal{ideal_label}Out : Vec Float {n_ideal_out}\n'
            'ideal{ideal_label}Out = {ideal_out}').format(
                ideal_label=ideal_label,
                n_ideal_in=n_ideal_in,
                n_ideal_out=n_ideal_out,
                ideal_in=convert_vector(ideal_in.tolist()),
                ideal_out=convert_vector(ideal_out.tolist()))

def convert_model(module_name, model, ideal):

    # Print layer definitions
    layer_defns = []
    layer_names = []
    n_in = None
    n_out = None
    for index, layer in enumerate(model.layers):
        params = layer.get_weights()
        if len(params) > 0:
            weights = params[0]
            rows = weights.shape[0]
            cols = weights.shape[1]
            layer_names.append('layer{}'.format(index))
            if n_in is None: n_in = rows
            n_out = cols
            layer_defns.append(convert_layer(index, layer))

    # Print model definition
    model_defn = convert_layer_list(layer_names, n_in, n_out)

    # Print ideals
    ideal_defns = []
    for ideal_label, ideal_data in ideal.items():
        ideal_in, ideal_out = ideal_data
        ideal_defns.append(convert_ideal(ideal_label, ideal_in, ideal_out))

    return ('module {module_name} where\n'
            '\n'
            'open import Data.Float\n'
            'open import Data.Vec\n'
            'open import Amethyst.Network\n'
            'open import Amethyst.Network.As.Float\n'
            '\n'
            '{layer_defns}\n'
            '\n'
            '{model_defn}\n'
            '\n'
            '{ideal_defns}\n'
            ).format(module_name=module_name,
                     layer_defns='\n\n'.join(layer_defns),
                     model_defn=model_defn,
                     ideal_defns='\n\n'.join(ideal_defns))

def main(model_file, agda_file, ideal_file=None):
    """Pretty-print a Keras models from a H5 file."""

    # Check for underscores in the filename:
    if '_' in agda_file:
        choice = input("Agda filenames should not contain underscores. Replace by '-'? [Y/n]").lower().strip()
        if not choice or choice[0] == 'y':
            agda_file = agda_file.replace('_', '-')
        else:
            print("Invalid output file: "+agda_file)

    # Open output file
    with open(agda_file, 'w') as os:

        module_name = Path(agda_file).resolve().stem
        model = load_model(model_file)

        if (ideal_file is None):
            ideal = {}
        else:
            with open(ideal_file, 'rb') as fp:
                ideal = pkl.load(fp)
                for ideal_label, ideal_data in ideal.items():
                    ideal_in, ideal_out = ideal_data

        os.write(convert_model(module_name, model, ideal))

def help():
    print('Usage: python convert.py [--with-ideal=[ideal_file]] -i [model_file] -o [agda_file]')
    sys.exit(2)

if __name__ == "__main__":
    model_file = None
    agda_file = None
    ideal_file = None
    try:
        opts, args = getopt(sys.argv[1:], "hi:o:", ["with-ideal="])
    except GetoptError:
        help()
    for opt, arg in opts:
        if opt == '-h': help()
        if opt == '-i': model_file = arg
        if opt == '-o': agda_file = arg
        if opt == '--with-ideal': ideal_file = arg
    if Path(model_file).is_file():
        if not (ideal_file is None or Path(ideal_file).is_file()):
            print("Error: file '" + ideal_file + "' not found.")
        main(model_file, agda_file, ideal_file=ideal_file)
    elif ifile is None:
        help()
    else:
        print("Error: file '" + model_file + "' not found.")
        sys.exit(3)
