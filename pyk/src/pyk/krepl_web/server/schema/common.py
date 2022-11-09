from graphene import InputObjectType, NonNull, String


class TermString(InputObjectType):
    term = NonNull(String)
    module = String()
    sort = String()


class BoolTermString(InputObjectType):
    term = NonNull(String)
    module = String()
