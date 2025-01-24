from unified_planning.environment import get_environment

up_env = get_environment()
up_env.factory.add_engine("tempest", "tempest.engine", "TempestEngine")
up_env.factory.add_engine("tempest-opt", "tempest.engine", "TempestOptimal")
up_env.credits_stream = None
