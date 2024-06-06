import sqlalchemy
import sqlalchemy.orm
import sqlalchemy.ext.declarative
from sqlalchemy.orm import scoped_session, sessionmaker


Base = sqlalchemy.ext.declarative.declarative_base()


class Test(Base):
    __tablename__ = "test"
    id = sqlalchemy.Column(sqlalchemy.Integer, primary_key=True)
    a = sqlalchemy.Column(sqlalchemy.Integer, nullable=False)
    b = sqlalchemy.Column(sqlalchemy.Integer, nullable=False)
    c = sqlalchemy.Column(
        sqlalchemy.Integer, sqlalchemy.Computed("a + b"), nullable=False
    )


engine = sqlalchemy.create_engine(f"postgresql://postgres:password@localhost/test")
Base.metadata.drop_all(bind=engine)
Base.metadata.create_all(bind=engine)

Session = scoped_session(sessionmaker(autocommit=False, autoflush=True, bind=engine))
session = Session()

session.add(Test(id=0, a=1, b=2))
session.commit()

print([(x.a, x.b, x.c) for x in session.query(Test).all()])

x = session.query(Test).filter(Test.id == 0).first()
x.a = 10
print((x.a, x.b, x.c))
session.commit()

print([(x.a, x.b, x.c) for x in session.query(Test).all()])
