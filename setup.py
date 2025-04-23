#!/usr/bin/env python3

from setuptools import setup # type: ignore

setup(name='tempest',
      version='0.0.1',
      description='',
      author='FBK PSO Unit',
      author_email='tamer@fbk.eu',
      url='tamer.fbk.eu',
      packages=['tempest', 'tempest.encoders'],
      python_requires='>=3.7',
      install_requires=["pysmt @ git+https://github.com/pysmt/pysmt@optimization"],
      license='Free For Educational Use',
      classifiers=[
          'License :: Free For Educational Use'
      ]
     )
